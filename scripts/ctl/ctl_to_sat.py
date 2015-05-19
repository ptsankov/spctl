#!/bin/python

from ctl_grammar import parseCTLFormula

DEFINED_FUNCTIONS = set()

def ctlToStr(formulaTree):
    if type(formulaTree) is str:
        return 'fun_' + formulaTree
    if formulaTree[0] == 'true':
        return 'fun_true' 
    return '_'.join([x.replace('!', 'neg').replace('->', 'implies').replace('&', 'and') if type(x) is str else ctlToStr(x) for x in formulaTree])

def ctlToSAT(ctlString, resourceGraph):
    ctlFormula = parseCTLFormula(ctlString)
    return ctlFormulaToSAT(ctlFormula, resourceGraph)

def ctlFormulaToSAT(formulaTree, resourceGraph):
    functionName = ctlToStr(formulaTree)
    if functionName in DEFINED_FUNCTIONS:
        return
    DEFINED_FUNCTIONS.add(functionName)
    
    if formulaTree[0] == 'true':
        print '(define-fun fun_true ((r Room) (o Bool) (v Bool)) Bool true)'
        return 'fun_true'
    elif formulaTree[0] == 'false':
        return
    elif formulaTree[0] == '!':
        subFormulaTree = formulaTree[1]
        subFormulaName = ctlToStr(subFormulaTree)
        ctlFormulaToSAT(subFormulaTree, resourceGraph)
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool (not ({} r o v)))'.format(functionName, subFormulaName)
    elif formulaTree[0] == '&':
        left = formulaTree[1]
        ctlFormulaToSAT(left, resourceGraph)
        right = formulaTree[2]
        ctlFormulaToSAT(right, resourceGraph)
        
        leftName = ctlToStr(left)
        rightName = ctlToStr(right)                
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool (and ({} r o v) ({} r o v)))'.format(functionName, leftName, rightName)
    elif formulaTree[0] == '->':
        left = formulaTree[1]
        ctlFormulaToSAT(left, resourceGraph)
        right = formulaTree[2]
        ctlFormulaToSAT(right, resourceGraph)
        
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
        ctlFormulaToSAT(left, resourceGraph)        
        right = formulaTree[2]                
        ctlFormulaToSAT(right, resourceGraph)
        
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
        ctlFormulaToSAT(equivFormulaTree, resourceGraph)
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool ({} r o v))'.format(functionName, equivFunctionName)                
    elif formulaTree[0] == 'AG':
        equivFormulaTree = ['!', ['EF', ['!', formulaTree[1]]]]
        equivFunctionName = ctlToStr(equivFormulaTree)
        ctlFormulaToSAT(equivFormulaTree, resourceGraph)
        print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool ({} r o v))'.format(functionName, equivFunctionName)
    elif formulaTree[0] == 'EG':
        raise NameError('TODO: EG')
    else:
        propName = formulaTree
        if propName in resourceGraph.nodes():
            print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool (= r {}))'.format(functionName, propName)
        elif propName == 'owner':
            print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool o)'.format(functionName)
        elif propName == 'visitor':
            print '(define-fun {} ((r Room) (o Bool) (v Bool)) Bool v)'.format(functionName)
        else:
            print 'Invalid proposition name'