#!/usr/bin/python
from ctl_grammar import parseCTLFormula
from utils import write


DEFINED_FUNCTIONS = set()
LONGEST_ACYCLIC_PATH = 3

def ctlToStr(formulaTree):
    if type(formulaTree) is str:
        return 'fun_' + formulaTree
    if formulaTree[0] == 'true':
        return 'fun_true' 
    return '_'.join([x.replace('!', 'neg').replace('->', 'implies').replace('&', 'and').replace('|', 'or') if type(x) is str else ctlToStr(x) for x in formulaTree])

def funParams(attrs):
    attrParams = ' '.join(['(room0 Room)'] + ['(' + attr + ' Bool)' for attr in attrs])    
    return '(' + attrParams + ')'

def ctlToSAT(ctlString, resGraph, attrs):    
    ctlFormula = parseCTLFormula(ctlString)    
    ctlFormulaToSAT(ctlFormula, resGraph, attrs)
    return ctlToStr(ctlFormula)
    

def ctlFormulaToSAT(formulaTree, resGraph, attrs):
    functionName = ctlToStr(formulaTree)
    if functionName in DEFINED_FUNCTIONS:
        return
    DEFINED_FUNCTIONS.add(functionName)
    if formulaTree[0] == 'true':
        write('(define-fun fun_true {} Bool true)\n'.format(funParams(attrs)))
    elif formulaTree[0] == 'false':
        raise NameError('TODO: False')
    elif formulaTree[0] == '!':
        subFormulaTree = formulaTree[1]
        subFormulaName = ctlToStr(subFormulaTree)
        ctlFormulaToSAT(subFormulaTree, resGraph, attrs)
        write('(define-fun {} {} Bool (not ({} {})))\n'.format(functionName, funParams(attrs), subFormulaName, ' '.join(['room0'] + attrs)))
    elif formulaTree[0] == '&':
        left = formulaTree[1]
        ctlFormulaToSAT(left, resGraph, attrs)
        right = formulaTree[2]
        ctlFormulaToSAT(right, resGraph, attrs)
        
        leftName = ctlToStr(left)
        rightName = ctlToStr(right)                
        write('(define-fun {} {} Bool (and ({} {}) ({} {})))\n'.format(functionName, funParams(attrs), leftName, ' '.join(['room0'] + attrs), rightName, ' '.join(['room0'] + attrs)))
    elif formulaTree[0] == '->':
        left = formulaTree[1]
        ctlFormulaToSAT(left, resGraph, attrs)
        right = formulaTree[2]
        ctlFormulaToSAT(right, resGraph, attrs)
        
        leftName = ctlToStr(left)
        rightName = ctlToStr(right)
        write('(define-fun {} {} Bool (=> ({} {}) ({} {})))\n'.format(functionName, funParams(attrs), leftName, ' '.join(['room0'] + attrs), rightName, ' '.join(['room0'] + attrs)))
    elif formulaTree[0] == '|':
        left = formulaTree[1]
        ctlFormulaToSAT(left, resGraph, attrs)
        right = formulaTree[2]
        ctlFormulaToSAT(right, resGraph, attrs)
        
        leftName = ctlToStr(left)
        rightName = ctlToStr(right)                
        write('(define-fun {} {} Bool (or ({} {}) ({} {})))\n'.format(functionName, funParams(attrs), leftName, ' '.join(['room0'] + attrs), rightName, ' '.join(['room0'] + attrs)))
    elif formulaTree[0] == 'AX':
        raise NameError('TODO: AX')
    elif formulaTree[0] == 'EX':
        raise NameError('TODO: EX')
    elif formulaTree[0] == 'AU':
        raise NameError('TODO: AU')
    elif formulaTree[0] == 'EU':                       
        left = formulaTree[1]        
        ctlFormulaToSAT(left, resGraph, attrs)        
        right = formulaTree[2]                
        ctlFormulaToSAT(right, resGraph, attrs)
        
        leftFunctionName = ctlToStr(left)
        rightFunctionName = ctlToStr(right)        
        write('(define-fun {} {} Bool\n'.format(functionName, funParams(attrs)))
        write('  (or\n')
        write('    ({} {})\n'.format(rightFunctionName, ' '.join(['room0'] + attrs)))
        for i in range(LONGEST_ACYCLIC_PATH):
            write('    (exists')
            write(' (' + ' '.join(['(room' + str(x+1) + ' Room)' for x in range(i+1)]) + ')')
            write(' (and ')
            write(' '.join(['(authz room' + str(x) + ' room' + str(x+1) + ' ' + ' '.join(attrs) + ')' for x in range(i+1)]))
            write(' ')
            write(' '.join(['(' + leftFunctionName + ' room' + str(x) + ' ' + ' '.join(attrs) + ')' for x in range(i+1)]))
            write(' ')
            write('({} {} {})'.format(rightFunctionName, 'room' + str(i+1), ' '.join(attrs)))
            write('))\n')
        write('  )\n')
        write(')\n')
    elif formulaTree[0] == 'AF':
        subformula = formulaTree[1]        
        ctlFormulaToSAT(subformula, resGraph, attrs)                
        subformulaName = ctlToStr(subformula)
        write('(define-fun {} {} Bool\n'.format(functionName, funParams(attrs)))
        write('  (forall (' + ' '.join(['(room' + str(x+1) + ' Room)' for x in range(LONGEST_ACYCLIC_PATH)]) + ')\n')
        write('    (-> (and ')
        write(' ')
        write(' '.join(['(authz room' + str(x) + ' room' + str(x+1) + ' ' + ' '.join(attrs) + ')' for x in range(LONGEST_ACYCLIC_PATH)]))
        write(' )\n')
        write('        (or ')
        write(' '.join(['(' + subformulaName + ' room' + str(x) + ' ' + ' '.join(attrs) + ')' for x in range(LONGEST_ACYCLIC_PATH + 1)]))
        write(' )\n')
        write('    )\n')
        write('  )\n')
        write(')\n')
    elif formulaTree[0] == 'EF':        
        equivFormulaTree = ['EU', ['true'], formulaTree[1]]
        equivFunctionName = ctlToStr(equivFormulaTree)
        ctlFormulaToSAT(equivFormulaTree, resGraph, attrs)
        write('(define-fun {} {} Bool ({} {}))\n'.format(functionName, funParams(attrs), equivFunctionName, ' '.join(['room0'] + attrs)))                
    elif formulaTree[0] == 'AG':
        equivFormulaTree = ['!', ['EF', ['!', formulaTree[1]]]]
        equivFunctionName = ctlToStr(equivFormulaTree)
        ctlFormulaToSAT(equivFormulaTree, resGraph, attrs)
        write('(define-fun {} {} Bool ({} {}))\n'.format(functionName, funParams(attrs), equivFunctionName, ' '.join(['room0'] + attrs)))
    elif formulaTree[0] == 'EG':
        equivFormulaTree = ['!', ['AF', ['!', formulaTree[1]]]]
        equivFunctionName = ctlToStr(equivFormulaTree)
        ctlFormulaToSAT(equivFormulaTree, resGraph, attrs)
        write('(define-fun {} {} Bool ({} {}))\n'.format(functionName, funParams(attrs), equivFunctionName, ' '.join(['room0'] + attrs)))
    else:
        propName = formulaTree
        if propName in resGraph.nodes():
            write('(define-fun {} {} Bool (= room0 {}))\n'.format(functionName, funParams(attrs), propName))
        elif propName in attrs:
            write('(define-fun {} {} Bool {})\n'.format(functionName, funParams(attrs), propName))
        else:
            raise NameError('Invalid proposition name')
