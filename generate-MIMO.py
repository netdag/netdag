from graph_tool import Graph, load_graph
from graph_tool.stats import remove_parallel_edges
from numpy.random import randint, random
from random import choice
from itertools import combinations as i_combinations

combinations = lambda x, k: list(i_combinations(x, k))

# generate the MIMO application for the paper

N_sense = 6
N_control = 3
N_actuate = 4

g = Graph()
g.add_vertex(n=N_sense+N_control+N_actuate)
# each controller senses from at least one location
for controller in range(N_control):
    g.add_edge(controller % N_sense, N_sense+controller)
# each sensor goes to at least one controller
for sensor in range(N_sense):
    for controller in choice(
        combinations(
            range(N_control),
            randint(
            1,
            N_control +
            1))):
        g.add_edge(sensor, N_sense+controller)
# each actuator receives control from at least on location
for actuator in range(N_actuate):
    g.add_edge((actuator % N_control)+N_sense, N_sense+N_control+actuator)
# # each controller goes to at least one actuator
# for controller in range(N_control):
#     for actuator in choice(
#         combinations(
#             range(N_actuate),
#             randint(
#             1,
#             N_actuate +
#             1))):
#         g.add_edge(
#             controller+N_sense,
#             N_sense+N_control+actuator)

remove_parallel_edges(g)
# if you don't do the following, you trigger a bug in new_edge_property
g.save('control-application.xml.gz')
g = load_graph('control-application.xml.gz')

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

# set soft real-time properties at the actuation tasks
for actuator in range(N_actuate):
    soft[N_sense+N_control+actuator] = 0.5 + random() / 2

g.vertex_properties['deadlines'] = deadlines
g.vertex_properties['durations'] = durations
g.vertex_properties['soft'] = soft
g.vertex_properties['weakly-hard'] = weakly_hard
g.edge_properties['widths'] = widths

g.save('control-application.xml.gz')
