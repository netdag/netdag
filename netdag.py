#!/usr/bin/python3
from sys import argv
from graph_tool import Graph, load_graph
from graph_tool.topology import is_DAG
from graph_tool.stats import remove_parallel_edges
from graph_tool.draw import graph_draw as draw
from itertools import product


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
    c_a_g = Graph()
    c_a_g.add_vertex(
        len(g.get_vertices()) +
        len(set(l_g.vertex_properties['CFOP_labeling'].get_array())))
    for e in g.edges():
        communication_vertex = l_g.vertex_properties[
            'CFOP_labeling'][g.edge_index[e]] + len(g.get_vertices())
        c_a_g.add_edge_list(
            [(e.source(), communication_vertex),
             (communication_vertex, e.target())])
    remove_parallel_edges(c_a_g)
    return c_a_g


if __name__ == '__main__':
    g = load_graph(argv[1])
    assert(is_DAG(g))
    draw(g, output='task_graph.png')
    l_g = line_graph(g)
    draw(l_g, output='line_graph.png')
    apply_simple_labeling(l_g)
    c_a_g = communication_adjusted(g, l_g)
    draw(c_a_g, output='comm_graph.png')
