#!/bin/python

from ctl_grammar import parseCTLFormula

DEFINED_FUNCTIONS = set()
LONGEST_ACYCLIC_PATH = 3
OUTPUT_FILE = None

def ctlToStr(formulaTree):
    if type(formulaTree) is str:
        return 'fun_' + formulaTree
    if formulaTree[0] == 'true':
        return 'fun_true' 
    return '_'.join([x.replace('!', 'neg').replace('->', 'implies').replace('&', 'and') if type(x) is str else ctlToStr(x) for x in formulaTree])

def funParams(attrs):
    attrParams = ' '.join(['(room Bool)'] + ['(' + attr + ' Bool)' for attr in attrs])    
    return '(' + attrParams + ')'

def ctlToSAT(ctlString, resGraph, attrs, outFile):
    global OUTPUT_FILE
    OUTPUT_FILE = outFile
    ctlFormula = parseCTLFormula(ctlString)
    return ctlFormulaToSAT(ctlFormula, resGraph, attrs)

def write(str):
    assert OUTPUT_FILE is not None
    OUTPUT_FILE.write(str)
    

def ctlFormulaToSAT(formulaTree, resGraph, attrs):
    functionName = ctlToStr(formulaTree)
    if functionName in DEFINED_FUNCTIONS:
        return
    DEFINED_FUNCTIONS.add(functionName)
    
    if formulaTree[0] == 'true':
        write('(define-fun fun_true {} Bool true)\n'.format(funParams(attrs)))
        return 'fun_true'
    elif formulaTree[0] == 'false':
        return
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
        raise NameError('TODO: |')
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
            write(' (and (distinct {})'.format(' '.join(['room' + str(x) for x in range(i+2)])))
            write(' ')
            write(' '.join(['(authz room' + str(x) + ' room' + str(x+1) + ' ' + ' '.join(attrs) + ')' for x in range(i+1)]))
            write(' ')
            write(' '.join(['(' + leftFunctionName + ' room' + str(x) + ' ' + ' '.join(attrs) + ')' for x in range(i+1)]))
            write(' ')
            write('({} {} {})'.format(rightFunctionName, 'room' + str(i+1), ' '.join(attrs)))
            write('))\n')
        #print '    (exists ((r1 Room)) (and (distinct r r1) ({} r o v) (authz r r1 o v) ({} r1 o v)))'.format(leftFunctionName, rightFunctionName)
        #print '    (exists ((r1 Room) (r2 Room)) (and (distinct r r1 r2) ({} r o v) (authz r r1 o v) ({} r1 o v) (authz r1 r2 o v) ({} r2 o v)))'.format(leftFunctionName, leftFunctionName, rightFunctionName)
        #print '    (exists ((r1 Room) (r2 Room) (r3 Room)) (and (distinct r r1 r2 r3) (authz r r1 o v) (authz r1 r2 o v) (authz r2 r3 o v) ({} r o v) ({} r1 o v) ({} r2 o v) ({} r3 o v)))'.format(leftFunctionName, leftFunctionName, leftFunctionName, rightFunctionName)
        write('  )\n')
        write(')\n')
    elif formulaTree[0] == 'AF':
        raise NameError('TODO: AF')
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
        raise NameError('TODO: EG')
    else:
        propName = formulaTree
        if propName in resGraph.nodes():
            write('(define-fun {} {} Bool (= room {}))\n'.format(functionName, funParams(attrs), propName))
        elif propName in attrs:
            write('(define-fun {} {} Bool {})\n'.format(functionName, funParams(attrs), propName))
        else:
            raise NameError('Invalid proposition name')
