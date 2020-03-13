import os
from pysmt.shortcuts import (
    Int, Symbol, Solver, Plus, And, Or, LE, LT, GT, Equals, NotEquals)
from pysmt.typing import INT
from numpy.random import randint, random
from numpy import logical_and, array, logical_or
from netdag import get_logical_edges
from graph_tool.topology import transitive_closure
from functools import reduce, partial


def check_WH(m, K, K_seq):
    return all((sum(K_seq[t:min(len(K_seq), t+K)]) <=
                m for t in range(max(1, len(K_seq)-K+1))))


def k_sequence_WH(m, K, K_seq_len=100, count=100):
    k_seq = [Symbol('x_%i' % i, INT) for i in range(K_seq_len)]
    domain = And([Or(Equals(x, Int(0)), Equals(x, Int(1))) for x in k_seq])
    K_window = And([LE(Plus(k_seq[t:min(K_seq_len, t+K)]), Int(m))
                    for t in range(max(1, K_seq_len-K+1))])
    formula = And(domain, K_window)
    solver = Solver(
        name='yices',
        incremental=True,
        random_seed=randint(
            2 << 30))
    solver.add_assertion(formula)
    for _ in range(count):
        result = solver.solve()
        if not result:
            solver = Solver(
                name='z3',
                incremental=True,
                random_seed=randint(
                    2 << 30))
            solver.add_assertion(formula)
            solver.solve()
        model = solver.get_model()
        model = array(
            list(map(lambda x: model.get_py_value(x), k_seq)), dtype=bool)
        yield model
        solver.add_assertion(Or([NotEquals(k_seq[i], Int(model[i]))
                                 for i in range(K_seq_len)]))


def k_sequence_WH_worst_case(m, K, K_seq_len=100, count=100):
    k_seq = [Symbol('x_%i' % i, INT) for i in range(K_seq_len)]
    domain = And([Or(Equals(x, Int(0)), Equals(x, Int(1))) for x in k_seq])
    K_window = And([LE(Plus(k_seq[t:min(K_seq_len, t+K)]), Int(m))
                    for t in range(max(1, K_seq_len-K+1))])
    violate_up = And([GT(Plus(k_seq[t:min(K_seq_len, t+K)]), Int(m-1))
                      for t in range(max(1, K_seq_len-K+1))])

    def violate_right_generator(n):
        return And([GT(Plus(k_seq[t:min(K_seq_len, t+K+n)]), Int(m))
                    for t in range(max(1, K_seq_len-(K+n)+1))])
    right_shift = 1
    formula = And(
        domain,
        K_window,
        violate_up,
        violate_right_generator(right_shift))
    solver = Solver(
        name='z3',
        incremental=True,
        random_seed=randint(
            2 << 30))
    solver.add_assertion(formula)
    solver.z3.set('timeout', 5*60*1000)
    solutions = And()
    for _ in range(count):
        while right_shift + K < K_seq_len:
            try:
                result = solver.solve()
            except BaseException:
                result = None
            if not result:
                solver = Solver(
                    name='z3',
                    incremental=True,
                    random_seed=randint(
                        2 << 30))
                right_shift += 1
                solver.z3.set('timeout', 5*60*1000)
                solver.add_assertion(And(solutions,
                                         domain,
                                         K_window,
                                         violate_up,
                                         violate_right_generator(right_shift)))
            else:
                break
        try:
            model = solver.get_model()
        except BaseException:
            break
        model = array(
            list(map(lambda x: model.get_py_value(x), k_seq)), dtype=bool)
        yield model
        solution = Or([NotEquals(k_seq[i], Int(model[i]))
                       for i in range(K_seq_len)])
        solutions = And(solutions, solution)
        solver.add_assertion(solution)


def k_sequence_WH_worker(x):
    fname = os.path.join('WH-traces', '%03d_%03d.txt' % x[::-1])
    if os.path.exists(fname):
        return x
    with open(fname, 'w') as f:
        [f.write(str(list(seq.astype(int))) + '\n')
         for seq in k_sequence_WH_worst_case(*x, K_seq_len=300, count=1000)]
    return x


def k_sequence_soft(p, K_seq_len=100):
    return random(size=K_seq_len) < p


def simulate_soft(g, model, lambda_s, N_iter=100):
    # N_iter is the total number of times the application will be run
    l_e = get_logical_edges(g)
    tc = transitive_closure(g)
    _, chi, _, label = model
    for v in g.vertices():
        parents = set([])
        soft = g.vertex_properties['soft'][v]
        if soft >= 0:
            for e in l_e:
                if e.source() in tc.get_in_neighbours(v):
                    parents.add(l_e.index(e))
                    parents.add(int(len(l_e)+label[l_e.index(e)]-1))
        if not parents:
            continue
        succ = sum(reduce(
                logical_and, [
                    k_sequence_soft(
                        lambda_s(
                            chi[i]), N_iter) for i in parents]))/N_iter
        print(
            '\t%i: simulated performance is %.02f%%, constraint was >%.02f%%' %
            (v, succ*100, soft*100))


def simulate_weakly_hard(g, model, lambda_wh, N_iter=100, K_seq_len=10):
    # N_iter is the total number of times the application will be run
    # K_seq_len stipulates the length of generated k-sequences, each of which
    # will be unique
    assert(N_iter % K_seq_len == 0)
    l_e = get_logical_edges(g)
    tc = transitive_closure(g)
    _, chi, _, label = model
    k_seq_WH_sim = partial(
        k_sequence_WH,
        K_seq_len=K_seq_len,
        count=N_iter//K_seq_len)
    for v in g.vertices():
        parents = set([])
        WH = g.vertex_properties['weakly-hard'][v]
        if WH[0] >= 0:
            for e in l_e:
                if e.source() in tc.get_in_neighbours(v):
                    parents.add(l_e.index(e))
                    parents.add(len(l_e)+label[l_e.index(e)]-1)
        if not parents:
            continue
        print(
            '\t%i: checking constraint ' %
            v,
            list(WH),
            '...',
            sep='',
            end=' ',
            flush=True)
        print(u'\u2713'
              if all(map(lambda x: check_WH(*WH, reduce(logical_or, x)),
                         zip(*(k_seq_WH_sim(*lambda_wh(chi[i]))
                               for i in parents))))
              else u'\u292C')


if __name__ == '__main__':
    from network_statistics import TEST_LAMBDA_SOFT as LAMBDA_SOFT
    from network_statistics import TEST_LAMBDA_WEAKLY_HARD as LAMBDA_WEAKLY_HARD
    from graph_tool import load_graph

    g = load_graph('simple-task-graph.xml.gz')
    model = (
        None, [
            3, 5, 5, 4, 4, 4, 1, 1, 1, 6, 6, 5, 4, 1, ], None, [
            3, 3, 4, 5, 5, 6, 7, ])
    print('*'*50+'\n\tSOFT\n'+'*'*50)
    simulate_soft(g, model, LAMBDA_SOFT, N_iter=10000)
    model = (
        None, [
            2, 1, 5, 5, 5, 5, 1, 5, 5, 1, 1, 5, 1, 1], None, [
            1, 1, 2, 2, 5, 5, 7])
    print('\n'+'*'*50+'\n\tWEAKLY-HARD\n'+'*'*50)
    simulate_weakly_hard(
        g,
        model,
        LAMBDA_WEAKLY_HARD,
        N_iter=10000,
        K_seq_len=100)
