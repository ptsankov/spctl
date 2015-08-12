'''
Created on Aug 12, 2015

@author: ptsankov
'''
from z3 import Bool, Solver, Function, BoolSort, Not, And, Or, Implies, sat
from ctl.ctl_to_sat import ctlToStr
import networkx as nx

INIT_RESOURCE = 'out'
EDGE_VARS = None
SOLVER = None
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

def encodeFormula(graph, ctlFormula, resource):
    print 'Encoding', ctlFormula, 'for resource', resource
    
       
    #function = karyFun(functionName, len(graph.edges()))
    #print function.sexpr()

    if ctlFormula in graph.nodes():
        if ctlFormula == resource:
            return True
        else:
            return False  
    elif ctlFormula[0] == 'true':
        return True
    elif ctlFormula[0] == 'false':
        return False
    elif ctlFormula[0] == 'not':
        subFormula = encodeFormula(graph, ctlFormula[1], resource)
        return Not(subFormula)
    elif ctlFormula[0] in ['and', 'or', '=>']:
        subFormulaLeft = encodeFormula(graph, ctlFormula[1], resource)
        subFormulaRight = encodeFormula(graph, ctlFormula[1], resource)
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
            return Or(pathConjuncts)                                
        else:
            raise NameError('Implement full support for the EF operator')
    elif ctlFormula[0] == 'EU':
        targetResources = graph.nodes()
        if ctlFormula[2] in graph.nodes():
            targetResources = [ctlFormula[2]]
        disjuncts = []
        for targetResource in targetResources:
            for path in nx.all_simple_paths(graph, resource, targetResource):        
                for i in range(len(path)):
                    conjuncts = []
                    conjuncts.append(encodeFormula(graph, ctlFormula[2], path[i]))
                    for j in range(0, i):
                        conjuncts.append(encodeFormula(graph, ctlFormula[1], path[j]))
                    edgePath = nodePathToEdgePath(graph, path[0:i])                   
                    conjuncts.append(And([EDGE_VARS[e] for e in edgePath]))
                    
                    SOLVER.reset()
                    SOLVER.add(And(conjuncts))
                    # simple check to avoid adding conjuncts that are always false
                    if SOLVER.check() == sat:                                        
                        disjuncts.append(And(conjuncts))
        return Or(disjuncts)
    elif ctlFormula[0] == 'AG':
        conjuncts = []
        for targetResource in graph.nodes():
            subFormula = encodeFormula(graph, ctlFormula[1], targetResource)
            SOLVER.reset()
            SOLVER.add(subFormula)
            if SOLVER.check() != sat:
                continue
            if targetResource == resource:
                conjuncts.append(subFormula)
            else:
                edgePathConditions = []
                for path in nx.all_simple_paths(graph, resource, targetResource):
                    edgePath = nodePathToEdgePath(graph, path)
                    edgeConjunct = And([EDGE_VARS[e] for e in edgePath])
                    edgePathConditions.append(edgeConjunct)                    
                pathExists = Or(edgePathConditions)
                conjuncts.append(Implies(pathExists, subFormula))
        return And(conjuncts)
    else:
        raise NameError('TODO: implement remaining CTL operators')
            
                     
# graph - a directed graph
# ctlFormulas - a list of CTL formulas
# returns the restricted graph that satisfies the formulas or unsat
def restrictGraph(graph, ctlFormulas):
    global DEFINED_FUNCTIONS, EDGE_VARS, SOLVER
    DEFINED_FUNCTIONS = set()
    print 'Restrict graph'    
    
    EDGE_VARS = {}    
    # declare variables for all edges
    for e in graph.edges():
        print e
        EDGE_VARS[e] = Bool(e[0] + '_' + e[1])
        
    SOLVER = Solver()
    for ctlFormula in ctlFormulas:
        print encodeFormula(graph, ctlFormula, INIT_RESOURCE)