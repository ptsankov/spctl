#!/usr/bin/python
from ctl_grammar import parseCTLFormula
from utils import write
import networkx as nx
from IN import TMP_MAX


DEFINED_FUNCTIONS = set()
LONGEST_ACYCLIC_PATH = 3

def ctlToStr(formulaTree, resource):
    if type(formulaTree) is str:
        return 'fun_' + formulaTree + '_' + resource
    if formulaTree[0] == 'true':
        return 'fun_true'    
    return '_'.join([x.replace('!', 'neg').replace('->', 'implies').replace('&', 'and').replace('|', 'or') if type(x) is str else ctlToStr(x, '') for x in formulaTree])  + '_' + resource

def funParams(attrs):
    attrParams = ' '.join(['(' + attr + ' Bool)' for attr in attrs])    
    return '(' + attrParams + ')'

def ctlToSAT(ctlString, resGraph, attrs, initResource):    
    ctlFormula = parseCTLFormula(ctlString)    
    ctlFormulaToSAT(ctlFormula, resGraph, attrs, initResource)
    return ctlToStr(ctlFormula, initResource)
    

def ctlFormulaToSAT(formulaTree, resGraph, attrs, resource):
    functionName = ctlToStr(formulaTree, resource)
    if functionName in DEFINED_FUNCTIONS:
        return
    DEFINED_FUNCTIONS.add(functionName)
    if formulaTree[0] == 'true':
        write('(define-fun fun_true {} Bool true)\n'.format(funParams(attrs)))
    elif formulaTree[0] == 'false':
        raise NameError('TODO: False')
    elif formulaTree[0] == '!':
        subFormulaTree = formulaTree[1]
        subFormulaName = ctlToStr(subFormulaTree, resource)
        ctlFormulaToSAT(subFormulaTree, resGraph, attrs, resource)
        write('(define-fun {} {} Bool (not ({} {})))\n'.format(functionName, funParams(attrs), subFormulaName, ' '.join(attrs)))
    elif formulaTree[0] == '&':
        left = formulaTree[1]
        ctlFormulaToSAT(left, resGraph, attrs, resource)
        right = formulaTree[2]
        ctlFormulaToSAT(right, resGraph, attrs, resource)
        
        leftName = ctlToStr(left, resource)
        rightName = ctlToStr(right, resource)                
        write('(define-fun {} {} Bool (and ({} {}) ({} {})))\n'.format(functionName, funParams(attrs), leftName, ' '.join(attrs), rightName, ' '.join(attrs)))
    elif formulaTree[0] == '->':
        left = formulaTree[1]
        ctlFormulaToSAT(left, resGraph, attrs, resource)
        right = formulaTree[2]
        ctlFormulaToSAT(right, resGraph, attrs, resource)
        
        leftName = ctlToStr(left, resource)
        rightName = ctlToStr(right, resource)
        write('(define-fun {} {} Bool (=> ({} {}) ({} {})))\n'.format(functionName, funParams(attrs), leftName, ' '.join(attrs), rightName, ' '.join(attrs)))
    elif formulaTree[0] == '|':
        left = formulaTree[1]
        ctlFormulaToSAT(left, resGraph, attrs, resource)
        right = formulaTree[2]
        ctlFormulaToSAT(right, resGraph, attrs, resource)
        
        leftName = ctlToStr(left, resource)
        rightName = ctlToStr(right, resource)                
        write('(define-fun {} {} Bool (or ({} {}) ({} {})))\n'.format(functionName, funParams(attrs), leftName, ' '.join(attrs), rightName, ' '.join(attrs)))
    elif formulaTree[0] == 'AX':
        raise NameError('TODO: AX')
    elif formulaTree[0] == 'EX':
        raise NameError('TODO: EX')
    elif formulaTree[0] == 'AU':
        raise NameError('TODO: AU')
    elif formulaTree[0] == 'EU':                            
        left = formulaTree[1]        
        right = formulaTree[2]
        for r in resGraph.nodes():
            print r
        raise NameError("todo")
        ctlFormulaToSAT(left, resGraph, attrs)                            
        ctlFormulaToSAT(right, resGraph, attrs)
        
        leftFunctionName = ctlToStr(left)
        rightFunctionName = ctlToStr(right)        
        write('(define-fun {} {} Bool\n'.format(functionName, funParams(attrs)))
        write('  (or\n')
        write('    ({} {})\n'.format(rightFunctionName, ' '.join(attrs)))
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
        raise NameError('remove quantifiers')
    elif formulaTree[0] == 'EF':
        if formulaTree[1] in resGraph.nodes():        
            targetResource = formulaTree[1]
            write('(define-fun {} {} Bool\n'.format(functionName, funParams(attrs)))
            write('  (or ')
            for path in nx.all_simple_paths(resGraph, resource, targetResource):
                write('    (and ')    
                for i in range(len(path)-1):
                    write('      (authz ' + path[i] + ' ' + path[i+1] + ' ' + ' '.join(attrs) + ')\n')
                write('    )\n')
            write('  )\n')
            write(')\n')
        else:
            subFormula = formulaTree[1]
            for r in resGraph.nodes():
                if r == resource:
                    continue                
                ctlFormulaToSAT(subFormula, resGraph, attrs, r)
            write('(define-fun {} {} Bool\n'.format(functionName, funParams(attrs)))
            write('  (or ')
            write('    false')
            for r in resGraph.nodes():
                if r == resource:
                    continue
                subFormulaName = ctlToStr(subFormula, r)
                for path in nx.all_simple_paths(resGraph, resource, r):
                    write('    (and ')
                    for i in range(len(path)-1):
                        write('        (authz ' + path[i] + ' ' + path[i+1] + ' ' + ' '.join(attrs) + ')\n')                    
                    write('      ({} {})\n'.format(subFormulaName, ' '.join(attrs)))
                    write('    )\n')
            write('  )\n')
            write(')\n')
    elif formulaTree[0] == 'AG':
        print 'AG'        
        subFormula = formulaTree[1]
        for r in resGraph.nodes():
            if r == resource:
                continue                        
            ctlFormulaToSAT(subFormula, resGraph, attrs, r)
        
        write('(define-fun {} {} Bool\n'.format(functionName, funParams(attrs)))
        write('  (and\n')
        for r in resGraph.nodes():
            if r == resource:
                continue            
            subFormulaName = ctlToStr(subFormula, r)
            print subFormula
            print r
            print subFormulaName            
            for path in nx.all_simple_paths(resGraph, resource, r):
                write('    (=>\n')
                write('      (and\n')
                for i in range(len(path)-1):
                    write('        (authz ' + path[i] + ' ' + path[i+1] + ' ' + ' '.join(attrs) + ')\n')                                
                write('      )\n')
                write('      ({} {})\n'.format(subFormulaName, ' '.join(attrs)))
                write('    )\n')
        write('  )\n')
        write(')\n')                
                
        '''
        equivFormulaTree = ['!', ['EF', ['!', formulaTree[1]]]]
        equivFunctionName = ctlToStr(equivFormulaTree)
        ctlFormulaToSAT(equivFormulaTree, resGraph, attrs)
        write('(define-fun {} {} Bool ({} {}))\n'.format(functionName, funParams(attrs), equivFunctionName, ' '.join(attrs)))
        '''
    elif formulaTree[0] == 'EG':
        raise NameError('implement optimizations')
    else:
        propName = formulaTree
        if propName in resGraph.nodes():
            write('(define-fun {} {} Bool (= {} {}))\n'.format(functionName, funParams(attrs), resource, propName))
        elif propName in attrs:
            write('(define-fun {} {} Bool {})\n'.format(functionName, funParams(attrs), propName))
        else:
            raise NameError('Invalid proposition name')
