#!/bin/python

import sys
import networkx as nx
import CTLGrammar

G = None
F = set()

def initGraph():
    global G
    G = nx.DiGraph()
    G.add_nodes_from(['out', 'lob', 'cor', 'off', 'mr'])
    G.add_edges_from([('out', 'lob'), ('out', 'cor')])
    G.add_edges_from([('lob', 'out'), ('lob', 'cor')])
    G.add_edges_from([('cor', 'lob'), ('cor', 'out'), ('cor', 'off'), ('cor', 'mr')])
    G.add_edge('off', 'cor')
    G.add_edge('mr', 'cor')

def ctlToStr(formulaTree):
    if type(formulaTree) is str:
        return 'fun_' + formulaTree
    if formulaTree[0] == 'true':
        return 'fun_true' 
    return '_'.join([x if type(x) is str else ctlToStr(x) for x in formulaTree])

def ctlToSAT(formulaTree):
    functionName = ctlToStr(formulaTree)
    if functionName in F:
        return
    F.add(functionName)
    
    if formulaTree[0] == 'true':
        print '(define-fun fun_true ((r Room) (o Bool) (v Bool)) Bool true)'
        return 'fun_true'
    elif formulaTree[0] == 'false':
        return
    elif formulaTree[0] == '!':
        print 'TODO: !'
    elif formulaTree[0] == '&':
        print 'TODO: &'
    elif formulaTree[0] == '->':
        print 'TODO: ->'
    elif formulaTree[0] == '|':
        print 'TODO: |'
    elif formulaTree[0] == 'AX':
        print 'TODO: AX'
    elif formulaTree[0] == 'EX':
        print 'TODO: EX'
    elif formulaTree[0] == 'AU':
        print 'TODO: AU'
    elif formulaTree[0] == 'EU':                        
        left = formulaTree[1]        
        ctlToSAT(left)        
        right = formulaTree[2]                
        ctlToSAT(right)
        
        leftFunctionName = ctlToStr(left)
        rightFunctionName = ctlToStr(right)        
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool'.format(functionName)
        print '  (or'
        print '    ({} r o v)'.format(rightFunctionName)
        print '    (exists ((r1 Room)) (and (distinct r r1) ({} r o v) (authz r r1 o v) ({} r1 o v)))'.format(leftFunctionName, rightFunctionName)
        print '    (exists ((r1 Room) (r2 Room)) (and (distinct r r1 r2) ({} r o v) (authz r r1 o v) ({} r1 o v) (authz r1 r2 o v) ({} r2 o v)))'.format(leftFunctionName, leftFunctionName, rightFunctionName)
        print '    (exists ((r1 Room) (r2 Room) (r3 Room)) (and (distinct r r1 r2 r3) ({} r o v) (authz r r1 o v) ({} r1 o v) (authz r1 r2 o v) ({} r2     o v) (authz r2 r3 o v) ({} r3 o v)))'.format(leftFunctionName, leftFunctionName, leftFunctionName, rightFunctionName)
        print '  )'
        print ')'
    elif formulaTree[0] == 'AF':
        print 'TODO: AF'
    elif formulaTree[0] == 'EF':        
        equivFormulaTree = ['EU', ['true'], formulaTree[1]]
        equivFunctionName = ctlToStr(equivFormulaTree)
        ctlToSAT(equivFormulaTree)
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool ({} r o v))'.format(functionName, equivFunctionName)                
    elif formulaTree[0] == 'AX':
        print 'TODO: AX'
    elif formulaTree[0] == 'EX':
        print 'TODO: EX'
    else:
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool (= r {}))'.format(functionName, formulaTree)
        

def main(argv):
    formulaString = '(EF off)'
    formulaTree = CTLGrammar.parseCTLFormula(formulaString)
    ctlToSAT(formulaTree)        
    
if __name__ == "__main__":
    initGraph()
    main(sys.argv[1:])    
