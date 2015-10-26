'''
Created on Sep 16, 2015

@author: ptsankov
'''


from networkx import *
if __name__ == '__main__':
    g = fast_gnp_random_graph(50, 0.01)
    #for n in g.nodes():
    #    print n
    #for e in g.edges():
    #    print e
    for n1 in g.nodes():
        for n2 in g.nodes():
            for p in all_simple_paths(g, n1, n2):
                print p
    