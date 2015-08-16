'''
Created on Aug 11, 2015

@author: ptsankov
'''
from z3 import unsat, Solver, sat, And, Not, simplify
from ctl.ctl_solver import encodeFormula, restrictGraph,\
    simplePathConditionFunction
from utils.helperMethods import INIT_RESOURCE, EDGE_VARS, strToZ3, setEdgeVars

def negativeSynth(graph, reqs):
    print 'Running the negative synthesis algorithm'
    setEdgeVars(graph)

    policy = {}
    for edge in graph.edges():
        policy[edge] = True
    
    for req in reqs:
        print 'Handling requirement', req
        
        propReq = req[0]
        
        s = Solver()       
        s.add(encodeFormula(graph, req, INIT_RESOURCE, simplePathConditionFunction))
        for e in graph.edges():
            s.add(EDGE_VARS[e] == True)
        if s.check() == sat:
            # must be a positive requirement
            print 'Skipping positive requirement'
            continue
        
        restrictedGraph = restrictGraph(graph, req)
        if restrictedGraph == unsat:
            return unsat
                    
        for removedEdge in list(set(graph.edges()) - set(restrictedGraph.edges())):
            policy[removedEdge] = simplify(And(policy[removedEdge], Not(strToZ3(propReq))))
    
    return policy