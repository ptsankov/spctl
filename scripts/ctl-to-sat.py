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
    return '_'.join([x if type(x) is str else ctlToStr(x) for x in formulaTree])

def ctlToSAT(formulaTree, state):
    print 'Processing formula tree:', formulaTree
    if formulaTree in M[state]:
        return
    M[state].append(formulaTree)
    if formulaTree[0] == 'true':
        print '(define-fun fun_true ((r Room) (o Bool) (v Bool)) Bool true)'
        return 'fun_true'
    elif formulaTree[0] == 'false':
        return
    elif formulaTree[0] == '!':
        print 'TODO: !'
    elif formulaTree[0] == '&':
        print 'TODO: &'
    elif formulaTree[0] == '|':
        print 'TODO: |'
    elif formulaTree[0] == 'AX':
        print 'TODO: AX'
    elif formulaTree[0] == 'EX':
        print 'TODO: EX'
    elif formulaTree[0] == 'AU':
        print 'TODO: AU'
    elif formulaTree[0] == 'EU':
        functionName = ctlToStr(formulaTree)        
        phi1 = formulaTree[1]
        phi2 = formulaTree[2]
        phi1Name = ctlToSAT(phi1, state)
        phi2Name = ctlToSAT(phi2, state)        
        phi2HoldsInCurrentState = '({} {} {} {})'.format(phi2Name, state, 'o', 'v')
        phi1HoldsInCurrentState = '({} {} {} {})'.format(phi1Name, state, 'o', 'v')
        forwardStates = [e[1] for e in G.edges() if e[0] == state]
        forwardStateFormulas = ['(and ({} {} {} {}) {} (edge {} o v))'.format(functionName, x, 'o', 'v', phi1HoldsInCurrentState, x) for x in forwardStates]
        orFormula = '(or {})'.format(' '.join([phi2HoldsInCurrentState] + forwardStateFormulas))
        print '(declare-fun {} (Room Bool Bool) Bool)'.format(functionName) 
        print '(assert (forall ((r Room) (o Bool) (v Bool)) {}))'.format(orFormula)
        return functionName
    elif formulaTree[0] == 'AF':
        print 'TODO: AF'
    elif formulaTree[0] == 'EF':
        subFormulaTree = formulaTree[1]
        rewriteFormulaTree = ['EU', ['true'], subFormulaTree]
        return ctlToSAT(rewriteFormulaTree, state)
    elif formulaTree[0] == 'AX':
        print 'TODO: AX'
    elif formulaTree[0] == 'EX':
        print 'TODO: EX'
    else:
        print '(define-fun fun_{} ((r Room) (o Bool) (v Bool)) Bool (= r {}))'.format(formulaTree, formulaTree)
        return 'fun_' + formulaTree
        

def main(argv):
    formulaString = '(EF off)'
    formulaTree = CTLGrammar.parseCTLFormula(formulaString)
    ctlToSAT(formulaTree, init)        
    
if __name__ == "__main__":
    initGraph()
    main(sys.argv[1:])    
