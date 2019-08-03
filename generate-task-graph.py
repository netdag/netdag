from subprocess import check_output, DEVNULL
from graph_tool import load_graph
from graph_tool.topology import transitive_closure
from io import StringIO
from numpy.random import randint, random, shuffle
from math import log
from functools import cmp_to_key

n = 100

f = StringIO('\n'.join(check_output(
    ['./daggen/daggen', '-n', str(n), '--fat', '.60,', '--density', '.1',
        '--jump', '1', '--dot'],
    stderr=DEVNULL).decode('ascii').split('\n')[2:]))

g = load_graph(f, fmt='dot')
del(g.vertex_properties['alpha'])
del(g.vertex_properties['vertex_name'])
del(g.vertex_properties['size'])
del(g.edge_properties['size'])
tc = transitive_closure(g)

deadlines = g.new_vertex_property('int')
durations = g.new_vertex_property('short')
soft = g.new_vertex_property('float')
weakly_hard = g.new_vertex_property('vector<short>')
widths = g.new_edge_property('short')

deadlines.get_array()[:] = -1
durations.get_array()[:] = randint(1, high=21, size=(g.num_vertices(),))
soft.get_array()[:] = -1
for v in g.vertices():
    weakly_hard[v] = [-1, 2000]
widths.get_array()[:] = randint(1, high=4, size=(g.num_edges(),))

_WH = {}
_soft = {}
v_select = list(range(g.num_vertices()))
shuffle(v_select)
v_select = sorted(
    v_select,
    key=cmp_to_key(
        lambda a,
        b: a in tc.get_in_neighbors(b)))
for v in v_select[:int(log(n))+1]:
    soft_bound = min([1.]+[_soft[u]
                           for u in _soft if u in tc.get_in_neighbors(v)])
    m_bound = max([0]+[_WH[u][0] for u in _WH if u in tc.get_in_neighbors(v)])
    K_bound = min([2000]+[_WH[u][1]
                          for u in _WH if u in tc.get_in_neighbors(v)])
    _soft[v] = soft_bound * random()
    soft[v] = _soft[v]
    _WH[v] = [None, None]
    _WH[v][0] = randint(m_bound, high=11)
    _WH[v][1] = randint(1000, high=K_bound+1)
    weakly_hard[v] = _WH[v]

g.vertex_properties['deadlines'] = deadlines
g.vertex_properties['durations'] = durations
g.vertex_properties['soft'] = soft
g.vertex_properties['weakly-hard'] = weakly_hard
g.edge_properties['widths'] = widths

g.save('complex-%03d-task-graph.xml.gz' % n)
