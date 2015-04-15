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
    G.add_edges_from([('out', 'lob'), ('out', 'cor'), ('out', 'out')])
    G.add_edges_from([('lob', 'out'), ('lob', 'cor'), ('lob', 'lob')])
    G.add_edges_from([('cor', 'lob'), ('cor', 'out'), ('cor', 'off'), ('cor', 'mr'), ('cor', 'cor')])
    G.add_edges_from([('off', 'cor'), ('off', 'off')])
    G.add_edges_from([('mr', 'cor'), ('mr', 'mr')])

def ctlToStr(formulaTree):
    if type(formulaTree) is str:
        return 'fun_' + formulaTree
    if formulaTree[0] == 'true':
        return 'fun_true' 
    return '_'.join([x.replace('!', 'neg').replace('->', 'implies').replace('&', 'and') if type(x) is str else ctlToStr(x) for x in formulaTree])

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
        subFormulaTree = formulaTree[1]
        subFormulaName = ctlToStr(subFormulaTree)
        ctlToSAT(subFormulaTree)
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool (not ({} r o v)))'.format(functionName, subFormulaName)
    elif formulaTree[0] == '&':
        left = formulaTree[1]
        ctlToSAT(left)
        right = formulaTree[2]
        ctlToSAT(right)
        
        leftName = ctlToStr(left)
        rightName = ctlToStr(right)                
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool (and ({} r o v) ({} r o v)))'.format(functionName, leftName, rightName)
    elif formulaTree[0] == '->':
        left = formulaTree[1]
        ctlToSAT(left)
        right = formulaTree[2]
        ctlToSAT(right)
        
        leftName = ctlToStr(left)
        rightName = ctlToStr(right)
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool (=> ({} r o v) ({} r o v)))'.format(functionName, leftName, rightName)
    elif formulaTree[0] == '|':
        raise NameError('TODO: |')
    elif formulaTree[0] == 'AX':
        raise NameError('TODO: AX')
    elif formulaTree[0] == 'EX':
        raise NameError('TODO: EX')
    elif formulaTree[0] == 'AU':
        raise NameError('TODO: AU')
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
    elif formulaTree[0] == 'AG':
        equivFormulaTree = ['!', ['EF', ['!', formulaTree[1]]]]
        equivFunctionName = ctlToStr(equivFormulaTree)
        ctlToSAT(equivFormulaTree)
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool ({} r o v))'.format(functionName, equivFunctionName)
    elif formulaTree[0] == 'EG':
        raise NameError('TODO: EG')
    else:
        propName = formulaTree
        if propName in G.nodes():
            print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool (= r {}))'.format(functionName, propName)
        elif propName == 'owner':
            print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool o)'.format(functionName)
        elif propName == 'visitor':
            print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool v)'.format(functionName)
        else:
            print 'Invalid proposition name'
        

def main(argv):
    ctlToSAT(CTLGrammar.parseCTLFormula('(-> (& owner out) (EF off))'))
    ctlToSAT(CTLGrammar.parseCTLFormula('(-> (& visitor out) (EF mr))'))
    ctlToSAT(CTLGrammar.parseCTLFormula('(-> (& visitor out) (! (EU (! lob) mr)))'))
    ctlToSAT(CTLGrammar.parseCTLFormula('(-> (& (! owner) out) (! (EF off)))'))
    ctlToSAT(CTLGrammar.parseCTLFormula('(AG (EF out))'))
    
if __name__ == "__main__":
    initGraph()
    main(sys.argv[1:])    
