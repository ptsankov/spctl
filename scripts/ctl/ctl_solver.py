'''
Created on Aug 12, 2015

@author: ptsankov
'''
from z3 import Solver, Not, And, Or, Implies, sat, unsat
import networkx as nx
from utils.helperMethods import EDGE_VARS, INIT_RESOURCE

def nodePathToEdgePath(graph, nodePath):
    edgePath = []
    for i in range(0, len(nodePath)-1):
        for e in graph.edges_iter(nodePath[i]):
            if e[1] == nodePath[i+1]:
                edgePath.append(e)                 
    return edgePath


def simplePathConditionFunction(graph, path, req):
    edgePath = nodePathToEdgePath(graph, path)
    edgeVars = [EDGE_VARS[e] for e in edgePath]
    return And(edgeVars)

def encodeFormula(graph, req, resource, pathConditionFunction):
    reqProp = req[0]
    reqCTL = req[1]
    #print 'encode', ctlFormula, 'for state', resource
    if reqCTL in graph.nodes():
        if reqCTL == resource:
            return True
        else:
            return False  
    elif reqCTL[0] == 'true':
        return True
    elif reqCTL[0] == 'false':
        return False
    elif reqCTL[0] == 'not':
        subFormula = encodeFormula(graph, [reqProp, reqCTL[1]], resource, pathConditionFunction)
        return Not(subFormula)
    elif reqCTL[0] in ['and', 'or', '=>']:
        subFormulaLeft = encodeFormula(graph, [reqProp, reqCTL[1]], resource, pathConditionFunction)
        subFormulaRight = encodeFormula(graph, [reqProp, reqCTL[2]], resource, pathConditionFunction)
        if reqCTL[0] == 'and':
            return And(subFormulaLeft, subFormulaRight)
        elif reqCTL[0] == 'or':
            return Or(subFormulaLeft, subFormulaRight)
        elif reqCTL[0] == '=>':
            return Implies(subFormulaLeft, subFormulaRight)
    elif reqCTL[0] == 'EF':
        if reqCTL[1] in graph.nodes():
            targetResource = reqCTL[1]
            pathDisjuncts = []
            for path in nx.all_simple_paths(graph, resource, targetResource):
                pathCondition = pathConditionFunction(graph, path, req)
                pathDisjuncts.append(pathCondition)
            return Or(pathDisjuncts)                                
        else:
            raise NameError('Implement full support for the EF operator')
    elif reqCTL[0] == 'EU':
        targetResources = graph.nodes()
        if reqCTL[2] in graph.nodes():
            targetResources = [reqCTL[2]]
        disjuncts = []
        for targetResource in targetResources:
            for path in nx.all_simple_paths(graph, resource, targetResource):
                for i in range(len(path)):
                    conjuncts = []
                    conjuncts.append(encodeFormula(graph, [reqProp, reqCTL[2]], path[i], pathConditionFunction))
                    for j in range(0, i):
                        conjuncts.append(encodeFormula(graph, [reqProp, reqCTL[1]], path[j], pathConditionFunction))
                    subpath = path[0:i]
                    pathCondition = pathConditionFunction(graph, subpath, req)            
                    conjuncts.append(pathCondition)                    
                    s = Solver()
                    s.add(And(conjuncts))
                    # add only if the condition is feasible
                    if s.check() == sat:                                        
                        disjuncts.append(And(conjuncts))
        return Or(disjuncts)
    elif reqCTL[0] == 'AG':
        conjuncts = []
        for targetResource in graph.nodes():
            subFormula = encodeFormula(graph, [reqProp, reqCTL[1]], targetResource, pathConditionFunction)
            s = Solver()
            s.add(subFormula)
            if s.check() != sat:
                continue
            if targetResource == resource:
                conjuncts.append(subFormula)
            else:
                edgePathConditions = []
                for path in nx.all_simple_paths(graph, resource, targetResource):                    
                    pathCondition = pathConditionFunction(graph, path, req)
                    edgePathConditions.append(pathCondition)                    
                pathExists = Or(edgePathConditions)
                conjuncts.append(Implies(pathExists, subFormula))
        return And(conjuncts)
    else:
        raise NameError('TODO: implement remaining CTL operators. Cannot handle ' + str(reqCTL))
            
                     
# graph - a directed graph
# req - a list of CTL formulas
# returns the restricted graph that satisfies the formulas or unsat
def restrictGraph(graph, req):    
    s = Solver()
    s.reset()
    s.add(encodeFormula(graph, req, INIT_RESOURCE, simplePathConditionFunction))
    
    for e in graph.edges():
        if e[0] == e[1]:
            s.add(EDGE_VARS[e] == True)
   
    if s.check() == sat:
        model = s.model()
        print model
        restrictedGraph = graph.copy()
        for e in graph.edges():
            if model[EDGE_VARS[e]] is not None and model[EDGE_VARS[e]].sexpr() == 'false':
                print 'removing edge', e
                restrictedGraph.remove_edge(e[0], e[1])
    else:
        return unsat
    return restrictedGraph
