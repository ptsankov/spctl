#!/usr/bin/python

import networkx
import copy
from mhlib import PATH
from networkx.algorithms.simple_paths import all_simple_paths

def remove_trivial_suffix(path):
    if path[len(path)-1] in path[:-1]:
        return remove_trivial_suffix(path[:-1])
    return path

def is_trivial_cycle(path, start_index, end_index):
    return False not in [path[cur_index] in path[:start_index] for cur_index in range(start_index+1, end_index)]

def remove_trivial_cycles(path):
    for start_index in range(len(path)):
        for end_index in range(start_index + 1, len(path)):
            if path[start_index] == path[end_index] and is_trivial_cycle(path, start_index, end_index):
                return remove_trivial_cycles(path[:start_index] + path[end_index:])
    return path             

def reduced_path(path):    
    return remove_trivial_cycles(remove_trivial_suffix(path))

def fixpoint_reduced_paths(g, reduced_paths):
    size = sum([len(reduced_paths[node]) for node in g.nodes()])
    copy_reduced_paths = copy.deepcopy(reduced_paths)
    for src in g.nodes():
        for src_path in copy_reduced_paths[src]:
            for trg_path in copy_reduced_paths[src_path[-1]]:
                new_path = src_path + trg_path[1:]
                reduced_paths[src].add(reduced_path(new_path))
                
    updated_size = sum([len(reduced_paths[node]) for node in g.nodes()])
    if updated_size != size:
        return fixpoint_reduced_paths(g, reduced_paths)
    return reduced_paths

def all_reduced_paths(g):
    reduced_paths = {}
    for node in g.nodes():
        reduced_paths[node] = set()
    for edge in g.edges():
        reduced_paths[edge[0]].add( (edge[0], edge[1]) )
    return fixpoint_reduced_paths(g, reduced_paths)
            

def main():    
    print "Computing reduced paths"
    g = networkx.DiGraph()
    g.add_node('out')
    g.add_node('lob')
    g.add_node('cor')
    g.add_node('mr')
    g.add_node('bur')
    g.add_edge('out', 'cor')
    g.add_edge('out', 'lob')
    g.add_edge('cor', 'out')
    g.add_edge('cor', 'lob')
    g.add_edge('cor', 'mr')
    g.add_edge('cor', 'bur')
    g.add_edge('mr', 'cor')
    g.add_edge('bur', 'cor')
    g.add_edge('lob', 'out')
    g.add_edge('lob', 'cor')
    print 'nodes', g.nodes()
    print 'edges', g.edges()

    x = 0
    for n1 in g.nodes():
        for n2 in g.nodes():
           for e in all_simple_paths(g, n1, n2):
               x += 1
    print 'all simple paths', x 
    
    reduced_paths = all_reduced_paths(g)
    print reduced_paths 
    for node in g.nodes():
        print len(reduced_paths[node]), reduced_paths[node]
            
    
if __name__ == '__main__':
    main()