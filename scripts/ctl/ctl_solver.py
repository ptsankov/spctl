'''
Created on Aug 12, 2015

@author: ptsankov
'''
from z3 import Bool, Solver, Function, BoolSort, Not, And, Or, Implies
from ctl.ctl_to_sat import ctlToStr
import networkx as nx

INIT_RESOURCE = 'out'
EDGE_VARS = None
DEFINED_FUNCTIONS = None

def karyFun(name, k):
    if k == 10:
        return Function(name, BoolSort(), BoolSort(), BoolSort(), BoolSort(), BoolSort(), BoolSort(), BoolSort(), BoolSort(), BoolSort(), BoolSort(), BoolSort())
    else:
        print 'Need to define the kary function'
        assert False

def nodePathToEdgePath(graph, nodePath):
    edgePath = []
    for i in range(0, len(nodePath)-1):
        for e in graph.edges_iter(nodePath[i]):
            if e[1] == nodePath[i+1]:
                edgePath.append(e)                 
    return edgePath

def encodeFormula(graph, ctlFormula, solver, resource):
    print 'Encoding', ctlFormula
    functionName = ctlToStr(ctlFormula, resource)
    print 'function name', functionName
    if functionName in DEFINED_FUNCTIONS:
        return
    
    DEFINED_FUNCTIONS.add(functionName)
        
    #function = karyFun(functionName, len(graph.edges()))
    #print function.sexpr()
    
    if ctlFormula[0] == 'true':
        return True
    elif ctlFormula[0] == 'false':
        return False
    elif ctlFormula[0] == 'not':
        subFormula = encodeFormula(graph, ctlFormula[1], solver, resource)
        return Not(subFormula)
    elif ctlFormula[0] in ['and', 'or', '=>']:
        subFormulaLeft = encodeFormula(graph, ctlFormula[1], solver, resource)
        subFormulaRight = encodeFormula(graph, ctlFormula[1], solver, resource)
        if ctlFormula[0] == 'and':
            return And(subFormulaLeft, subFormulaRight)
        elif ctlFormula[0] == 'or':
            return Or(subFormulaLeft, subFormulaRight)
        elif ctlFormula[0] == '=>':
            return Implies(subFormulaLeft, subFormulaRight)
    elif ctlFormula[0] == 'EF':
        if ctlFormula[1] in graph.nodes():
            targetResource = ctlFormula[1]
            pathConjuncts = []
            for path in nx.all_simple_paths(graph, resource, targetResource):
                edgePath = nodePathToEdgePath(graph, path)
                conjunct = And([EDGE_VARS[e] for e in edgePath])
                pathConjuncts.append(conjunct)
            print 'path conjuncts', pathConjuncts
            return Or(pathConjuncts)                                
        else:
            print 'TODO'
            assert False
# graph - a directed graph
# ctlFormulas - a list of CTL formulas
# returns the restricted graph that satisfies the formulas or unsat
def restrictGraph(graph, ctlFormulas):
    global DEFINED_FUNCTIONS, EDGE_VARS
    DEFINED_FUNCTIONS = set()
    print 'Restrict graph'    
    
    EDGE_VARS = {}    
    # declare variables for all edges
    for e in graph.edges():
        print e
        EDGE_VARS[e] = Bool(e[0] + '_' + e[1])
        
    solver = Solver()
    for ctlFormula in ctlFormulas:
        encodeFormula(graph, ctlFormula, solver, INIT_RESOURCE)