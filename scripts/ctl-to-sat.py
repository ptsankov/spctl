#!/bin/python

import sys
import networkx as nx
import CTLGrammar

G = None
init = 'out'
M = {}

def initGraph():
    global G
    G = nx.DiGraph()
    G.add_nodes_from(['out', 'lob', 'cor', 'off', 'mr'])
    G.add_edges_from([('out', 'lob'), ('out', 'cor')])
    G.add_edges_from([('lob', 'out'), ('lob', 'cor')])
    G.add_edges_from([('cor', 'lob'), ('cor', 'out'), ('cor', 'off'), ('cor', 'mr')])
    G.add_edge('off', 'cor')
    G.add_edge('mr', 'cor')
    for n in G.nodes():
        M[n] = []

def ctlToStr(formulaTree):
    return '_'.join(formulaTree)

def ctlToSAT(formulaTree, state):
    print ctlToStr(formulaTree)
    if formulaTree in M[state]:
        return
    M[state].append(formulaTree)
    if formulaTree[0] == 'true':
        return
    elif formulaTree[0] == 'false':
        return
    elif formulaTree[0] == '!':
        print 'pass'
    elif formulaTree[0] == '&':
        print 'pass'
    elif formulaTree[0] == '|':
        print 'pass'
    elif formulaTree[0] == 'AX':
        print 'pass'
    elif formulaTree[0] == 'EX':
        print 'pass'
    elif formulaTree[0] == 'AU':
        print 'pass'
    elif formulaTree[0] == 'EU':
        print 'pass'
    elif formulaTree[0] == 'AF':
        print 'pass'
    elif formulaTree[0] == 'EF':
        print 'pass'
    elif formulaTree[0] == 'AX':
        print 'pass'
    elif formulaTree[0] == 'EX':
        print 'pass'
    else:
        print ctlToStr(formulaTree, state) + ' <-> ' + state + ' = ' + formulaTree[0] 
        

def main(argv):
    formulaString = '(EF out)'
    formulaTree = CTLGrammar.parseCTLFormula(formulaString)
    ctlToSAT(formulaTree, init)        
    
if __name__ == "__main__":
    initGraph()
    main(sys.argv[1:])    
