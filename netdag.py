__copyright__ = """
    Copyright 2020 Boston University Board of Trustees

    Author: Kacper Wardega
"""

__license__ = """
    This file is part of netdag.

    netdag is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    netdag is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with netdag.  If not, see <https://www.gnu.org/licenses/>.
"""

from sys import argv
from graph_tool import load_graph
from graph_tool.topology import is_DAG, transitive_closure
from graph_tool.draw import graph_draw
from pysmt.typing import INT
from pysmt.shortcuts import (
    Solver,
    Symbol,
    Int,
    GE,
    LE,
    GT,
    LT,
    Minus,
    Plus,
    Times,
    Min,
    Equals,
    And,
    Or,
    Implies,
    Iff,
    Ite,
    ForAll)
from pysmt.solvers.solver import SolverReturnedUnknownResultError
from cvxpy import (
    matmul,
    Variable,
    Minimize,
    Problem)
from cvxpy import sum as cvxsum
from cvxpy import max as cvxmax
from numpy import array, ceil
from drawSvg import Drawing, Rectangle, Text, Line
from colour import Color
from itertools import product, chain
from network_statistics import LOG
from network_statistics import TEST_LAMBDA_SOFT as LAMBDA_SOFT
from network_statistics import TEST_LAMBDA_WEAKLY_HARD as LAMBDA_WEAKLY_HARD


verbose = True
vprint = print if verbose else lambda *a, **k: None


def draw_schedule(g, model, filename):
    zeta, chi, duration, label = model
    TOP = 30
    BOTTOM = 30
    LEFT = 100
    RIGHT = 30
    WIDTH = 800
    HEIGHT = 800
    ROW_OFFSET = 20
    TEXT_OFFSET = 40
    FONTSIZE = 30
    d = Drawing(WIDTH, HEIGHT)
    d.append(Rectangle(0, 0, WIDTH, HEIGHT, fill='white'))
    N_tasks = g.num_vertices()
    N_rounds = len(zeta) - N_tasks
    min_t = min(
        zeta[:N_tasks] - g.vertex_properties['durations'].get_array())
    max_t = max(zeta)
    quantum = (WIDTH-RIGHT-LEFT) / (max_t-min_t)
    block_height = (HEIGHT-TOP-BOTTOM-ROW_OFFSET*(N_tasks)) / (N_tasks+1)
    for i in range(N_tasks):
        color = list(
            Color('red').range_to('green', 1000))[
                max(0, int(g.vertex_properties['soft'][i]*999))]
        d.append(Rectangle(
            quantum*abs(min_t) + LEFT+quantum*(zeta[i] -
                                               g.vertex_properties[
                                                   'durations'][i]),
            HEIGHT-TOP-ROW_OFFSET*i-block_height*(i+1),
            quantum*g.vertex_properties['durations'][i],
            block_height,
            fill=color.get_hex_l(),
            stroke_width=2,
            stroke='black'))
        if g.vertex_properties['deadlines'][i] >= 0:
            x = quantum*abs(min_t) + LEFT+quantum*(
                g.vertex_properties['deadlines'][i])
            d.append(
                Line(x, HEIGHT-TOP-ROW_OFFSET*i-block_height*(i+1),
                     x, HEIGHT-TOP-ROW_OFFSET*i-block_height*i,
                     stroke_width=4,
                     stroke='purple'))

        d.append(
            Text(
                str(i),
                FONTSIZE, TEXT_OFFSET, HEIGHT - TOP - ROW_OFFSET * i -
                block_height * (i + 1) + block_height / 2, center=True,
                fill='black'))
    for i in range(N_rounds):
        if duration[i] == 0:
            continue
        d.append(Rectangle(
            quantum*abs(min_t)+LEFT+quantum*(zeta[N_tasks+i] -
                                             duration[i]),
            HEIGHT-TOP-ROW_OFFSET*N_tasks-block_height*(N_tasks+1),
            quantum*duration[i],
            block_height,
            fill='gray',
            stroke_width=2,
            stroke='black'))
    d.append(
        Text(
            'LWB',
            FONTSIZE, TEXT_OFFSET, HEIGHT - TOP - ROW_OFFSET * N_tasks -
            block_height * (N_tasks + 1) + block_height / 2, center=True,
            fill='black'))
    d.savePng(filename)


def get_logical_edges(g):
    sources = set([])
    logical_edges = []
    for e in g.edges():
        if e.source() not in sources:
            logical_edges.append(e)
            sources.add(e.source())
    return logical_edges


def get_makespan_optimal_soft_schedule(g, network):
    vprint('*computing optimal soft real-time schedule via MIP*')
    # MILP formulation
    tc = transitive_closure(g)
    logical_edges = get_logical_edges(g)
    JUMPTABLE_MAX = 20
    A, B, C, D, GAMMA, LAMBDA = (network[key]
                                 for key in
                                 ('A', 'B', 'C', 'D', 'GAMMA', 'LAMBDA'))
    M = 1000

    vprint('\tinstantiating symvars...')
    label = Variable(shape=(len(logical_edges),), integer=True)
    # first half for slot, second half for beacons
    chi = Variable(shape=(2*len(logical_edges),), integer=True)
    duration = Variable(shape=(len(logical_edges),), integer=True)
    zeta = Variable(shape=(g.num_vertices()+len(logical_edges),), integer=True)
    delta_e_in_r = Variable(
        shape=(
            len(logical_edges),
            len(logical_edges)),
        boolean=True)
    delta_chi_eq_i = Variable(
        shape=(
            2*len(logical_edges),
            JUMPTABLE_MAX),
        boolean=True)
    delta_e_in_r_cross_chi_eq_i = {(e, r): Variable(
        shape=(
            2*len(logical_edges),
            JUMPTABLE_MAX))
        for e, r in product(range(len(logical_edges)), repeat=2)}
    delta_tau_before_r = Variable(
        shape=(
            g.num_vertices()+len(logical_edges),
            len(logical_edges)),
        boolean=True)
    delta_empty = Variable(shape=(len(logical_edges),), boolean=True)

    vprint('\tgenerating constraint clauses...')
    vprint('\t\tdomain')
    domain = [
        1 <= label,
        label <= len(logical_edges),
        1 <= chi,
        chi <= JUMPTABLE_MAX-1,
        0 <= zeta]
    vprint('\t\tone_hot')
    one_hot = [
        cvxsum(delta_e_in_r, axis=1) == 1,
        cvxsum(delta_chi_eq_i, axis=1) == 1]
    vprint('\t\tCFOP')
    CFOP = [
        label[logical_edges.index(r)] <= label[logical_edges.index(s)] - 1
        for r, s in product(logical_edges, repeat=2)
        if r.source() in tc.get_in_neighbors(s.source())]
    vprint('\t\ttask_partitioning_by_round')
    task_partitioning_by_round = [
        delta_tau_before_r[int(tau)][r] <= delta_tau_before_r[int(mu)][r]
        for tau, mu, r in
        product(tc.vertices(), tc.vertices(), range(len(logical_edges)))
        if tau in tc.get_in_neighbors(mu)]
    task_partitioning_by_round += [
        delta_tau_before_r[r+g.num_vertices()][s] == 0
        if r < s else delta_tau_before_r[r+g.num_vertices()][s] == 1
        for r, s in product(range(len(logical_edges)), repeat=2)]
    vprint('\t\tround_empty')
    round_empty = [
        chi[len(logical_edges):] <= M * cvxsum(delta_e_in_r, axis=0) + 1]
    round_empty_to_delta = [
        delta_empty[r] <= 1 - delta_e_in_r[e][r]
        for r, e in product(range(len(logical_edges)), repeat=2)]
    round_empty_to_delta += [
        delta_empty >= cvxsum(1-delta_e_in_r, axis=0)-len(logical_edges)+1]
    vprint('\t\tdurations')
    durations = [
        duration[r] == A +
        (2 * chi[r + len(logical_edges)] + B) * (C + D * GAMMA) -
        delta_empty[r] * (A + (2 + B) * (C + D * GAMMA)) +
        sum(
            [A * delta_e_in_r[e][r] +
             (2 *
              sum(
                  [i * delta_e_in_r_cross_chi_eq_i[(e, r)][e][i]
                   for i in range(JUMPTABLE_MAX)]) + B * delta_e_in_r[e][r]) *
             (C + D * g.edge_properties['widths'][logical_edges[e]])
             for e in range(len(logical_edges))])
        for r in range(len(logical_edges))]
    vprint('\t\tlabel_to_delta')
    label_to_delta = [
        label == matmul(
            delta_e_in_r,
            array(
                range(1,
                      1+len(logical_edges))))]
    vprint('\t\tchi_to_delta')
    chi_to_delta = [
        chi == matmul(
            delta_chi_eq_i,
            array(range(JUMPTABLE_MAX)))]
    vprint('\t\tbinary_mult_linearization')
    binary_mult_linearization = list(chain.from_iterable(
        [[0 <= delta_e_in_r_cross_chi_eq_i[(e, r)][chir][i],
          delta_e_in_r_cross_chi_eq_i[(e, r)][chir][i] <= 1,
          delta_e_in_r_cross_chi_eq_i[(e, r)][chir][i] <= delta_e_in_r[e][r],
          delta_e_in_r_cross_chi_eq_i[(e, r)][chir][i] <=
          delta_chi_eq_i[chir][i],
          delta_e_in_r_cross_chi_eq_i[(e, r)][chir][i] >=
          delta_e_in_r[e][r] + delta_chi_eq_i[chir][i] - 1]
         for e, r, chir, i in
         product(
             range(len(logical_edges)),
             range(len(logical_edges)),
             range(2*len(logical_edges)),
             range(JUMPTABLE_MAX))]))
    vprint('\t\torder')
    order = [
        zeta[int(tau)] <= zeta[int(mu)] - g.vertex_properties['durations'][mu] -
        1 for tau, mu in product(g.vertices(),
                                 repeat=2)
        if tau in tc.get_in_neighbors(mu)]
    order += [
        zeta[r + g.num_vertices()] <= zeta[r + 1 + g.num_vertices()] -
        duration[r + 1] - 1 for r in range(len(logical_edges) - 1)]
    # the following two can be re-written using delta_tau_before_r ?
    order += [
        zeta[int(tau)] - g.vertex_properties['durations'][tau] -
        zeta[r + g.num_vertices()] - 1 >= -M * (1-delta_e_in_r[e][r])
        for tau in g.vertices()
        for r in range(len(logical_edges)) for e in range(len(logical_edges))
        if tau in tc.get_out_neighbors(logical_edges[e].source())]
    order += [
        zeta[r+g.num_vertices()] - duration[r] - zeta[int(tau)] - 1 >= -M *
        (1-delta_e_in_r[e][r])
        for tau in g.vertices()
        for r, e in product(range(len(logical_edges)), repeat=2)
        if tau in tc.get_in_neighbors(logical_edges[e].source()) or
        tau == logical_edges[e].source()]
    vprint('\t\texclusion')
    exclusion = list(chain.from_iterable(
        [[-M * delta_tau_before_r[int(tau)][r] <=
          zeta[r + g.num_vertices()] - duration[r] - zeta[int(tau)] - 1,
          M * (1 - delta_tau_before_r[int(tau)][r]) + zeta[int(tau)] -
          g.vertex_properties['durations'][tau] - 1 >=
          zeta[g.num_vertices() + r]]
         for tau in g.vertices()
         for r in range(len(logical_edges))]))
    vprint('\t\tsoft')
    soft = [LOG(g.vertex_properties['soft'][tau]) <=
            sum([delta_e_in_r_cross_chi_eq_i[(e, r)][len(logical_edges)+r][i] *
                 LOG(LAMBDA(i))
                 for i in range(1, JUMPTABLE_MAX)
                 for r in range(len(logical_edges))
                 for e in range(len(logical_edges))
                 if logical_edges[e].source() in tc.get_in_neighbors(tau)]) +
            sum([delta_chi_eq_i[e][i]*LOG(LAMBDA(i))
                 for e in range(len(logical_edges))
                 for i in range(1, JUMPTABLE_MAX)
                 if logical_edges[e].source() in tc.get_in_neighbors(tau)])
            for tau in g.vertices()
            if g.vertex_properties['soft'][tau] >= 0]
    soft = list(filter(lambda x: type(x) != bool, soft))
    vprint('\t\tdeadline')
    deadline = [zeta[int(tau)] <= g.vertex_properties['deadlines'][tau]
                for tau in g.vertices()
                if g.vertex_properties['deadlines'][tau] >= 0]

    constraints = domain + one_hot + CFOP + round_empty_to_delta + \
        chi_to_delta + binary_mult_linearization + round_empty + \
        task_partitioning_by_round + label_to_delta + order + durations + \
        exclusion + soft + deadline
    # print(all(map(lambda x: x.is_dcp(), constraints)))
    # print('DEBUG: exiting...')
    # exit()
    vprint('\tsending to solver...')
    objective = Minimize(cvxmax(zeta))
    problem = Problem(objective, constraints)
    # focus on improving the bound, limit 100GB for storing nodes, aggresively generate all cut types
    problem.solve(solver='GUROBI', verbose=True, MIPFocus=3, NodefileStart=100, Cuts=2)
    vprint('\tsolver returned ' + problem.status + '!')
    return zeta.value, chi.value, duration.value, label.value


def get_makespan_optimal_weakly_hard_schedule(g, network, feasibility_timeout=None, optimization_timeout=10*60*1000):
    vprint('*computing optimal weakly-hard real-time schedule via SMT*')
    # SMT formulation
    tc = transitive_closure(g)
    logical_edges = get_logical_edges(g)
    JUMPTABLE_MAX = 6
    K_MAX = 5001  # LAMBDA(i)[1] < K_MAX for all i < JUMPTABLE_MAX

    A, B, C, D, GAMMA, LAMBDA = (network[key]
                                 for key in
                                 ('A', 'B', 'C', 'D', 'GAMMA', 'LAMBDA'))

    assert(all(map(lambda x: LAMBDA(x)[1] < K_MAX, range(JUMPTABLE_MAX))))

    vprint('\tinstantiating symvars...')
    label = [Symbol('label_%i' % i, INT) for i in range(len(logical_edges))]
    # first half for slot, second half for beacons
    chi = [Symbol('chi_%i' % i, INT) for i in range(2*len(logical_edges))]
    duration = [Symbol('duration_%i' % i, INT)
                for i in range(len(logical_edges))]
    zeta = [Symbol('zeta_%i' % i, INT)
            for i in range(g.num_vertices()+len(logical_edges))]
    delta_e_in_r = [[Symbol('delta_e_in_r-%i_%i' % (i, j), INT)
                     for j in range(len(logical_edges))]
                    for i in range(len(logical_edges))]
    delta_chi_eq_i = [[Symbol('delta_chi_eq_i-%i_%i' % (i, j), INT)
                       for j in range(JUMPTABLE_MAX)]
                      for i in range(2*len(logical_edges))]
    delta_tau_before_r = [[Symbol('delta_tau_before_r-%i_%i' % (i, j), INT)
                           for j in range(len(logical_edges))]
                          for i in range(g.num_vertices()+len(logical_edges))]

    vprint('\tgenerating constraint clauses...')
    domain = And([
        And([And(LE(Int(1), sym), LE(sym, Int(len(logical_edges))))
             for sym in label]),
        And([And(LE(Int(1), sym), LT(sym, Int(JUMPTABLE_MAX))) for sym in chi]),
        And([LE(Int(0), sym) for sym in zeta]),
        And([And(LE(Int(0), sym), LE(sym, Int(1)))
             for sym in
             chain.from_iterable(
                 delta_e_in_r + delta_chi_eq_i + delta_tau_before_r)])])
    one_hot = And([
        And([Equals(
            Plus([delta_e_in_r[e][r] for r in range(len(logical_edges))]),
            Int(1))
             for e in range(len(logical_edges))]),
        And([Equals(
            Plus([delta_chi_eq_i[chir][i] for i in range(JUMPTABLE_MAX)]),
            Int(1))
             for chir in range(2*len(logical_edges))])])
    CFOP = And([
        LT(label[logical_edges.index(r)], label[logical_edges.index(s)])
        for r, s in product(logical_edges, repeat=2)
        if r.source() in tc.get_in_neighbors(s.source())])
    task_partitioning_by_round = And(
        And([
            LE(delta_tau_before_r[int(tau)][r], delta_tau_before_r[int(mu)][r])
            for tau, mu, r in
            product(tc.vertices(), tc.vertices(), range(len(logical_edges)))
            if tau in tc.get_in_neighbors(mu)]),
        And([
            Equals(delta_tau_before_r[r+g.num_vertices()][s], Int(0))
            if r < s else
            Equals(delta_tau_before_r[r+g.num_vertices()][s], Int(1))
            for r, s in product(range(len(logical_edges)), repeat=2)]))
    round_empty = And([
        Implies(
            Equals(Plus([delta_e_in_r[e][r]
                         for e in range(len(logical_edges))]), Int(0)),
            Equals(chi[len(logical_edges)+r], Int(1)))
        for r in range(len(logical_edges))])
    durations = And([
        Equals(
            duration[r],
            Plus(
                Int(A),
                Times(
                    Plus(Times(Int(2), chi[r+len(logical_edges)]), Int(B)),
                    Int(C+D*GAMMA)),
                Times(
                    Ite(
                        GE(
                            Plus([delta_e_in_r[e][r]
                                  for e in range(len(logical_edges))]),
                            Int(1)),
                        Int(0),
                        Int(-1)),
                    Int(A+(2+B)*(C+D*GAMMA))),
                Plus([
                    Ite(
                        Equals(delta_e_in_r[e][r], Int(1)),
                        Plus(
                            Int(A),
                            Times(
                                Plus(Times(Int(2), chi[e]), Int(B)),
                                Int(C +
                                    D*g.edge_properties['widths'][
                                        logical_edges[e]]))),
                        Int(0))
                    for e in range(len(logical_edges))])))
        for r in range(len(logical_edges))])
    label_to_delta = And([
        Equals(
            label[e],
            Plus([Times(delta_e_in_r[e][i-1], Int(i))
                  for i in range(1, 1+len(logical_edges))]))
        for e in range(len(logical_edges))])
    chi_to_delta = And([
        Equals(
            chi[chir],
            Plus([Times(delta_chi_eq_i[chir][i], Int(i))
                  for i in range(JUMPTABLE_MAX)]))
        for chir in range(2*len(logical_edges))])
    order = And(
        And([
            LT(
                zeta[int(tau)],
                Minus(zeta[int(mu)],
                      Int(g.vertex_properties['durations'][mu])))
            for tau, mu in product(g.vertices(), repeat=2)
            if tau in tc.get_in_neighbors(mu)]),
        And([
            LT(
                zeta[r+g.num_vertices()],
                Minus(zeta[r+1+g.num_vertices()],
                      duration[r+1]))
            for r in range(len(logical_edges) - 1)]),
        And([
            Implies(
                Equals(delta_e_in_r[e][r], Int(1)),
                GT(
                    Minus(zeta[int(tau)],
                          Int(g.vertex_properties['durations'][tau])),
                    zeta[r+g.num_vertices()]))
            for tau in g.vertices()
            for r in range(len(logical_edges))
            for e in range(len(logical_edges))
            if tau in tc.get_out_neighbors(logical_edges[e].source())]),
        And([
            Implies(
                Equals(delta_e_in_r[e][r], Int(1)),
                GT(
                    Minus(zeta[r+g.num_vertices()],
                          duration[r]),
                    zeta[int(tau)]))
            for tau in g.vertices()
            for r in range(len(logical_edges))
            for e in range(len(logical_edges))
            if tau in tc.get_in_neighbors(logical_edges[e].source()) or
            tau == logical_edges[e].source()]))
    exclusion = And([
        And(
            Implies(
                Equals(delta_tau_before_r[int(tau)][r], Int(0)),
                GT(
                    Minus(zeta[r+g.num_vertices()], duration[r]),
                    zeta[int(tau)])),
            Implies(
                Equals(delta_tau_before_r[int(tau)][r], Int(1)),
                GT(
                    Minus(zeta[int(tau)],
                          Int(g.vertex_properties['durations'][tau])),
                    zeta[g.num_vertices()+r])))
        for tau in g.vertices()
        for r in range(len(logical_edges))])
    deadline = And([
        LE(zeta[int(tau)], Int(g.vertex_properties['deadlines'][tau]))
        for tau in g.vertices()
        if g.vertex_properties['deadlines'][tau] >= 0
    ])

    def sum_m(tau): return Plus([Int(0)]+[
        Plus(
            Ite(
                Equals(delta_chi_eq_i[e][i], Int(1)),
                Int(LAMBDA(i)[0]),
                Int(0)),
            Plus([
                Ite(
                    Equals(delta_chi_eq_i[len(logical_edges)+r][i], Int(1)),
                    Ite(
                        Equals(delta_e_in_r[e][r], Int(1)),
                        Int(LAMBDA(i)[0]),
                        Int(0)),
                    Int(0))
                for r in range(len(logical_edges))]))
        for i in range(JUMPTABLE_MAX)
        for e in range(len(logical_edges))
        if logical_edges[e].source() in
        tc.get_in_neighbors(tau)])

    def min_K(tau): return Min([Int(K_MAX)]+[
        Min(
            Ite(
                Equals(delta_chi_eq_i[e][i], Int(1)),
                Int(LAMBDA(i)[1]),
                Int(K_MAX)),
            Min([
                Ite(
                    Equals(delta_chi_eq_i[len(logical_edges)+r][i], Int(1)),
                    Ite(Equals(delta_e_in_r[e][r], Int(1)),
                        Int(LAMBDA(i)[1]),
                        Int(K_MAX)),
                    Int(K_MAX))
                for r in range(len(logical_edges))]))
        for i in range(JUMPTABLE_MAX)
        for r in range(len(logical_edges))
        for e in range(len(logical_edges))
        if logical_edges[e].source() in
        tc.get_in_neighbors(tau)])
    WH = And([
        And(
            GE(Int(g.vertex_properties['weakly-hard'][tau][0]),
               Min(
                   sum_m(tau),
                   min_K(tau))),
            LE(Int(g.vertex_properties['weakly-hard'][tau][1]),
               min_K(tau)))
        for tau in g.vertices()
        if g.vertex_properties['weakly-hard'][tau][0] >= 0])

    formula = And([
        domain, one_hot, CFOP, task_partitioning_by_round, round_empty,
        durations, label_to_delta, chi_to_delta, order, exclusion, deadline,
        WH
    ])
    vprint('\tchecking feasibility...')
    solver = Solver(name='z3', incremental=True, logic='LIA')
    if feasibility_timeout:
        solver.z3.set('timeout', feasibility_timeout)
    solver.add_assertion(formula)
    try:
        result = solver.solve()
    except SolverReturnedUnknownResultError:
        result = None
    if not result:
        vprint('\tsolver returned infeasible!')
        return [None] * 4
    else:
        models = [solver.get_model()]
        vprint('\tsolver found a feasible solution, optimizing...')

    solver.z3.set('timeout', optimization_timeout)
    LB = 0
    UB = max(map(lambda x: models[-1].get_py_value(x), zeta))
    curr_B = UB // 2
    while range(LB+1, UB):
        try:
            result = solver.solve([And([LT(zeta_tau, Int(curr_B))
                                        for zeta_tau in zeta])])
        except SolverReturnedUnknownResultError:
            vprint('\t(timeout, not necessarily unsat)')
            result = None
        if result:
            vprint('\tfound feasible solution of length %i, optimizing...' %
                   curr_B)
            models.append(solver.get_model())
            UB = curr_B
        else:
            vprint('\tnew lower bound %i, optimizing...' % curr_B)
            LB = curr_B
        curr_B = LB + int(ceil((UB - LB) / 2))
    vprint('\tsolver returned optimal (under composition+P.O. abstractions)!')
    best_model = models[-1]
    zeta = list(map(lambda x: best_model.get_py_value(x), zeta))
    chi = list(map(lambda x: best_model.get_py_value(x), chi))
    duration = list(map(lambda x: best_model.get_py_value(x), duration))
    label = list(map(lambda x: best_model.get_py_value(x), label))
    return zeta, chi, duration, label


if __name__ == '__main__':
    vprint('loading graph...')
    g = load_graph(argv[1])
    vprint('checking DAG...')
    assert(is_DAG(g))
    graph_draw(
        g,
        output=argv[1] +
        '_task-graph.png',
        vertex_text=g.vertex_index,
        vertex_font_size=18)
