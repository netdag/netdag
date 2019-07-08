#!/usr/bin/python3
from sys import argv
from graph_tool import Graph, load_graph
from graph_tool.topology import is_DAG, transitive_closure
from graph_tool.stats import remove_parallel_edges
from graph_tool.draw import graph_draw
from graph_tool.util import find_edge
from pysmt.typing import INT, REAL
from pysmt.shortcuts import (
    get_model,
    Symbol,
    GE,
    LE,
    Int,
    Real,
    And,
    Or,
    Implies,
    Minus,
    GT,
    LT,
    Bool,
    Plus,
    Times,
    Equals,
    NotEquals,
    ForAll)
from drawSvg import Drawing, Rectangle, Text, Line
from itertools import product
from enum import IntEnum
from network_statistics import LOG
from network_statistics import TEST_GAMMA as GAMMA
from network_statistics import TEST_D_N as D_N
from network_statistics import TEST_LAMBDA as LAMBDA
from network_statistics import TEST_BETA as BETA


class NodeType(IntEnum):
    TASK = 0
    COMMUNICATION = 1


def apply_simple_labeling(l_g):
    CFOP_labeling = l_g.new_vertex_property('int16_t')
    curr_label = 0
    open = set((l_g.get_in_degrees(l_g.get_vertices()) == 0).nonzero()[0])
    while open:
        closed = set()
        while open:
            node = open.pop()
            CFOP_labeling[node] = curr_label
            closed.add(node)
        curr_label += 1
        while closed:
            open.update(l_g.get_out_neighbors(closed.pop()))
    l_g.vertex_properties['CFOP_labeling'] = CFOP_labeling


def line_graph(g):
    l_g = Graph()
    l_g.add_vertex(g.edge_index_range)
    for e, f in product(g.edges(), repeat=2):
        if e.target() == f.source():
            l_g.add_edge(g.edge_index[e], g.edge_index[f])
    return l_g


def communication_adjusted(g, l_g):
    communication_rounds = set(
        l_g.vertex_properties['CFOP_labeling'].get_array())
    assert(max(communication_rounds) == len(communication_rounds) - 1)
    c_a_g = Graph()
    c_a_g.add_vertex(len(g.get_vertices()) + len(communication_rounds))
    for e in g.edges():
        communication_vertex = l_g.vertex_properties[
            'CFOP_labeling'][g.edge_index[e]] + len(g.get_vertices())
        c_a_g.add_edge_list(
            [(e.source(), communication_vertex),
             (communication_vertex, e.target())])
    remove_parallel_edges(c_a_g)
    vprops = c_a_g.new_vertex_property('object')
    for tau in g.vertices():
        vprops[tau] = {
            'type': int(NodeType.TASK),
            'duration': g.vertex_properties['durations'][tau],
            'soft': g.vertex_properties['soft'][tau],
            'weakly-hard': g.vertex_properties['weakly-hard'][tau]}
    for r in communication_rounds:
        vprops[len(g.get_vertices())+r] = {
            'type': int(NodeType.COMMUNICATION),
            'width': sum([g.edge_properties['widths'][
                find_edge(g, g.edge_index, l_g.vertex_index[e])[0]]
                for e in l_g.vertices()
                if l_g.vertex_properties['CFOP_labeling'][e] == r])}
    c_a_g.vertex_properties['vprops'] = vprops
    return c_a_g


def symbolic_app_agnostic_schedule(c_a_g, gamma, D_N):
    N_tasks = sum(map(lambda x: c_a_g.vertex_properties['vprops'][
                  x]['type'] == NodeType.TASK, c_a_g.vertices()))
    tc = transitive_closure(c_a_g)

    zeta = [Symbol('zeta_%d' % i, INT) for i in c_a_g.vertices()]
    chi = [
        Symbol('chi_%d' % i, INT) for i in c_a_g.vertices()
        if c_a_g.vertex_properties['vprops'][i]['type'] ==
        NodeType.COMMUNICATION]
    duration = [Symbol('duration_%d' % i, INT) for i in c_a_g.vertices()]

    domains = And([GE(symvar, Int(0)) for symvar in zeta] +
                  [GE(symvar, Int(D_N)) for symvar in chi])
    order = And([
                 Implies(
                     Bool(mu in tc.get_out_neighbors(tau)),
                     GT(Minus(zeta[int(mu)],
                              duration[int(mu)]),
                        zeta[int(tau)])) for tau,
                 mu in product(tc.vertices(),
                               repeat=2)])
    durations = And(
        [
         Equals(
             duration[int(i)],
             Int(c_a_g.vertex_properties['vprops'][i]['duration']))
         if c_a_g.vertex_properties['vprops'][i]['type'] == NodeType.TASK else
         Equals(
             duration[int(i)],
             Plus(
                 Int(gamma),
                 Times(
                     chi[int(i) - N_tasks],
                     Int(c_a_g.vertex_properties['vprops'][i]['width']))))
         for i in c_a_g.vertices()])

    exclusion = And([
        Or(LT(zeta[s], Minus(zeta[r], duration[r])),
           GT(Minus(zeta[s], duration[s]), zeta[r]))
        for s, r in product(
            range(c_a_g.num_vertices()), range(N_tasks, c_a_g.num_vertices()))
        if s != r])

    formula = And(domains, order, durations, exclusion)

    return formula, {'zeta': zeta, 'chi': chi, 'duration': duration}


def symbolic_app_soft_schedule(c_a_g, symvars, LAMBDA, D_N):
    JUMPTABLE_MAX = 10
    for i in range(D_N, JUMPTABLE_MAX):
        assert(LAMBDA(i) > 0)
    zeta, chi, duration = [symvars[key] for key in ['zeta', 'chi', 'duration']]
    N_tasks = len(zeta) - len(chi)
    tc = transitive_closure(c_a_g)
    log_lam = [Symbol('log_lam_%d' % i, REAL) for i in range(len(chi))]

    domain = And([LT(chi_r, Int(JUMPTABLE_MAX)) for chi_r in chi])
    jumptable = And([
        Implies(
            Equals(chi_r, Int(i)),
            Equals(log_lam_r, Real(LOG(LAMBDA(i)))))
        for i, (chi_r, log_lam_r)
        in product(range(JUMPTABLE_MAX), zip(chi, log_lam))
        if LAMBDA(i) > 0])
    soft = And([
                LE(
                    Real(LOG(c_a_g.vertex_properties['vprops'][tau]['soft'])),
                    Plus(
                        [Real(LOG(1.))] +
                        [log_lam[int(i) - N_tasks] for i in c_a_g.vertices()
                         if i in tc.get_in_neighbors(tau) and
                         c_a_g.vertex_properties['vprops'][i]['type'] ==
                         NodeType.COMMUNICATION]))
                for tau in range(N_tasks)])

    formula = And(domain, jumptable, soft)
    return formula


def symbolic_app_weakly_hard_schedule(c_a_g, symvars, BETA):
    JUMPTABLE_MAX = 10
    zeta, chi, duration = [symvars[key] for key in ['zeta', 'chi', 'duration']]
    N_tasks = len(zeta) - len(chi)
    tc = transitive_closure(c_a_g)
    beta = [[Symbol('beta_%d-0' % i, INT), Symbol('beta_%d-1' % i, INT)]
            for i in range(len(chi))]
    omega = {tau:
             {int(alpha):
              [Symbol('omega(%d)_%d-%d' % (tau, alpha, i), INT)
               for i in
               range(c_a_g.vertex_properties['vprops'][tau]['weakly-hard'][1])]
              for alpha in c_a_g.vertices()
              if int(alpha) == tau or
              (alpha in tc.get_in_neighbors(tau) and
               c_a_g.vertex_properties['vprops'][alpha]['type'] ==
               NodeType.COMMUNICATION)}
             for tau in range(N_tasks)}

    domain = And([LT(chi_r, Int(JUMPTABLE_MAX)) for chi_r in chi])
    jumptable = And([
        Implies(
            Equals(chi_r, Int(i)),
            And(
                Equals(beta_r[0], Int(BETA(i)[0])),
                Equals(beta_r[1], Int(BETA(i)[1]))))
        for i, (chi_r, beta_r)
        in product(range(JUMPTABLE_MAX), zip(chi, beta))])
    WH = And([
        ForAll(
            [omega_tau_alpha_i
             for omega_tau_alpha in omega[tau].values()
             for omega_tau_alpha_i in omega_tau_alpha],
            Implies(And(
                And([Or(
                    Equals(omega_tau_alpha_i, Int(0)),
                    Equals(omega_tau_alpha_i, Int(1)))
                    for omega_tau in omega.values()
                    for omega_tau_alpha in omega_tau.values()
                    for omega_tau_alpha_i in omega_tau_alpha]),
                And([And([
                    Implies(
                        Equals(Int(chi_c), chi[r-N_tasks]),
                        And([LE(
                            Plus([Int(0)]+[omega[tau][r][i]
                                           for i in
                                           range(t,
                                                 min(t+BETA(chi_c)[1],
                                                     c_a_g.
                                                     vertex_properties[
                                                         'vprops'][tau][
                                                             'weakly-hard'][
                                                                 1]))]),
                            Int(BETA(chi_c)[0]))
                            for t in
                            range(
                                max(1,
                                    c_a_g.vertex_properties[
                                        'vprops'][tau][
                                            'weakly-hard'][1] -
                                    BETA(chi_c)[1]))]))
                    for chi_c in range(JUMPTABLE_MAX)])
                    for r in omega[tau]
                    if r != tau]),
                And([Implies(
                    Or([Bool(False)] +
                       [Equals(omega[tau][r][t], Int(1))
                        for r in omega[tau] if r != tau]),
                    Equals(omega[tau][tau][t], Int(1)))
                    for t in
                    range(c_a_g.vertex_properties[
                        'vprops'][tau]['weakly-hard'][1])])),
                    LE(Plus(omega[tau][tau]),
                       Int(c_a_g.vertex_properties[
                           'vprops'][tau]['weakly-hard'][0]))))
        for tau in range(N_tasks)
        if tc.get_in_degrees([tau])[0] > 0])

    formula = And(domain, jumptable, WH)
    return formula


def draw_schedule(c_a_g, model, symvars, gamma, filename):
    zeta, chi, duration = [symvars[key] for key in ['zeta', 'chi', 'duration']]
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
    N_tasks = len(zeta) - len(chi)
    min_t = min(map(lambda x: model.get_py_value(
        x[0])-model.get_py_value(x[1]), zip(zeta, duration)))
    max_t = max(map(lambda x: model.get_py_value(x), zeta))
    quantum = (WIDTH-RIGHT-LEFT) / (max_t-min_t)
    block_height = (HEIGHT-TOP-BOTTOM-ROW_OFFSET*(N_tasks)) / (N_tasks+1)
    for i in range(N_tasks):
        d.append(Rectangle(
            quantum*abs(min_t) + LEFT+quantum*(model.get_py_value(zeta[i]) -
                                               model.get_py_value(duration[i])),
            HEIGHT-TOP-ROW_OFFSET*i-block_height*(i+1),
            quantum*model.get_py_value(duration[i]),
            block_height,
            fill='green',
            stroke_width=2,
            stroke='black'))
        d.append(
            Text(
                str(i),
                FONTSIZE, TEXT_OFFSET, HEIGHT - TOP - ROW_OFFSET * i -
                block_height * (i + 1) + block_height / 2, center=True,
                fill='black'))
    for i in range(N_tasks, c_a_g.num_vertices()):
        d.append(Rectangle(
            quantum*abs(min_t)+LEFT+quantum*(model.get_py_value(zeta[i]) -
                                             model.get_py_value(duration[i])),
            HEIGHT-TOP-ROW_OFFSET*N_tasks-block_height*(N_tasks+1),
            quantum*model.get_py_value(duration[i]),
            block_height,
            fill='red',
            stroke_width=2,
            stroke='black'))
        d.append(Rectangle(
            quantum*abs(min_t)+LEFT+quantum*(model.get_py_value(zeta[i]) -
                                             model.get_py_value(duration[i])),
            HEIGHT-TOP-ROW_OFFSET*N_tasks-block_height*(N_tasks+1),
            quantum*gamma,
            block_height,
            fill='yellow',
            stroke_width=2,
            stroke='black'))
        for j in range(1, model.get_py_value(chi[i-N_tasks])):
            round_width = (model.get_py_value(
                duration[i])-gamma)/model.get_py_value(chi[i-N_tasks])
            x = LEFT+quantum*(abs(min_t)+(model.get_py_value(
                zeta[i]) - model.get_py_value(duration[i]))+gamma+j*round_width)
            d.append(
                Line(
                    x, HEIGHT - TOP - ROW_OFFSET * N_tasks - block_height *
                    (N_tasks + 1),
                    x, HEIGHT - TOP - ROW_OFFSET * N_tasks - block_height *
                    N_tasks, stroke='black', stroke_width=2))
    d.append(
        Text(
            'LWB',
            FONTSIZE, TEXT_OFFSET, HEIGHT - TOP - ROW_OFFSET * N_tasks -
            block_height * (N_tasks + 1) + block_height / 2, center=True,
            fill='black'))
    d.savePng(filename)


def get_optimal_model_fixed_labeling(formula, symvars, upper_bound=None):
    if upper_bound:
        formula = formula.And(And([LT(zeta_tau, Int(upper_bound))
                                   for zeta_tau in symvars['zeta']]))
    models = [get_model(formula, solver_name='z3')]
    if not models[-1]:
        return None
    while models[-1]:
        schedule_length = max(
            map(lambda x: models[-1].get_py_value(x), symvars['zeta']))
        formula = formula.And(And([LT(zeta_tau, Int(schedule_length))
                                   for zeta_tau in symvars['zeta']]))
        models.append(get_model(formula, solver_name='z3'))
    return models[-2]


def apply_CFOP_labeling(l_g, labels):
    CFOP_labeling = l_g.new_vertex_property('int16_t')
    CFOP_labeling.get_array()[:] = labels
    l_g.vertex_properties['CFOP_labeling'] = CFOP_labeling


def get_optimal_agnostic_schedule(g, l_g, gamma, D_N):
    UB = None
    best_model = None
    best_symvars = None
    best_labeling = None
    for labeling in enumerate_labelings(l_g):
        apply_CFOP_labeling(l_g, labeling)
        c_a_g = communication_adjusted(g, l_g)
        formula, symvars = symbolic_app_agnostic_schedule(c_a_g, gamma, D_N)
        model = get_optimal_model_fixed_labeling(
            formula, symvars, upper_bound=UB)
        if model:
            schedule_length = max(
                map(lambda x: model.get_py_value(x), symvars['zeta']))
            if not UB or schedule_length < UB:
                UB = schedule_length
                best_model = model
                best_symvars = symvars
                best_labeling = labeling
    return best_model, best_symvars, best_labeling


def get_optimal_soft_schedule(g, l_g, gamma, D_N, performance_function):
    UB = None
    best_model = None
    best_symvars = None
    best_labeling = None
    for labeling in enumerate_labelings(l_g):
        apply_CFOP_labeling(l_g, labeling)
        c_a_g = communication_adjusted(g, l_g)
        formula, symvars = symbolic_app_agnostic_schedule(c_a_g, gamma, D_N)
        formula = formula.And(
            symbolic_app_soft_schedule(
                c_a_g, symvars, performance_function, D_N))
        model = get_optimal_model_fixed_labeling(
            formula, symvars, upper_bound=UB)
        if model:
            schedule_length = max(
                map(lambda x: model.get_py_value(x), symvars['zeta']))
            if not UB or schedule_length < UB:
                UB = schedule_length
                best_model = model
                best_symvars = symvars
                best_labeling = labeling
    return best_model, best_symvars, best_labeling


def get_optimal_weakly_hard_schedule(g, l_g, gamma, D_N, performance_function):
    UB = None
    best_model = None
    best_symvars = None
    best_labeling = None
    for labeling in enumerate_labelings(l_g):
        apply_CFOP_labeling(l_g, labeling)
        c_a_g = communication_adjusted(g, l_g)
        formula, symvars = symbolic_app_agnostic_schedule(c_a_g, gamma, D_N)
        formula = formula.And(
            symbolic_app_weakly_hard_schedule(
                c_a_g, symvars, performance_function))
        model = get_optimal_model_fixed_labeling(
            formula, symvars, upper_bound=UB)
        if model:
            schedule_length = max(
                map(lambda x: model.get_py_value(x), symvars['zeta']))
            if not UB or schedule_length < UB:
                UB = schedule_length
                best_model = model
                best_symvars = symvars
                best_labeling = labeling
    return best_model, best_symvars, best_labeling


def enumerate_labelings(l_g):
    tc = transitive_closure(l_g)
    apply_simple_labeling(l_g)
    LB = max(l_g.vertex_properties['CFOP_labeling']) + 1
    UB = l_g.num_vertices()
    labels = [Symbol('label_%d' % i, INT) for i in range(UB)]
    structure = And([Implies(Bool(r in tc.get_in_neighbors(s)),
                             LT(labels[r], labels[s]))
                     for r, s in product(range(UB), repeat=2)])
    for codomain_size in range(LB, UB+1):
        codomain = And(
            And([Or([
                Equals(label, Int(i))
                for label in labels])
                for i in range(codomain_size)]),
            And([
                And(
                    LT(label, Int(codomain_size)),
                    GE(label, Int(0)))
                for label in labels]))
        formula = And(structure, codomain)
        while True:
            model = get_model(formula, solver_name='z3')
            if not model:
                break
            yield [model.get_py_value(label) for label in labels]
            formula = formula.And(Or([
                NotEquals(label, Int(model.get_py_value(label)))
                for label in labels]))

if __name__ == '__main__':
    g = load_graph(argv[1])
    assert(is_DAG(g))
    graph_draw(
        g,
        output=argv[1] +
        '_task_graph.png',
        vertex_text=g.vertex_index,
        vertex_font_size=18)
    l_g = line_graph(g)

    model, symvars, labeling = get_optimal_agnostic_schedule(g, l_g, GAMMA, D_N)
    apply_CFOP_labeling(l_g, labeling)
    draw_schedule(
        communication_adjusted(g, l_g),
        model,
        symvars,
        GAMMA,
        argv[1] +
        '_schedule_agnostic.png')

    model, symvars, labeling = get_optimal_soft_schedule(
        g, l_g, GAMMA, D_N, LAMBDA)
    apply_CFOP_labeling(l_g, labeling)
    draw_schedule(
        communication_adjusted(g, l_g),
        model,
        symvars,
        GAMMA,
        argv[1] +
        '_schedule_soft.png')

    model, symvars, labeling = get_optimal_weakly_hard_schedule(
        g, l_g, GAMMA, D_N, BETA)
    apply_CFOP_labeling(l_g, labeling)
    draw_schedule(
        communication_adjusted(g, l_g),
        model,
        symvars,
        GAMMA,
        argv[1] +
        '_schedule_weakly_hard.png')
