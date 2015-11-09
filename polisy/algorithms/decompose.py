'''
Created on Aug 11, 2015

@author: ptsankov
'''
from algorithms.controller import restrictGraph, declareEdgeVars
from itertools import chain, combinations
from z3 import And, Not, simplify
from algorithms.smt import strToZ3
  
 
def synth(graph, reqs):
    print 'Running the decompose synthesis algorithm'
    print reqs

    reqs = set(reqs)

    policy = {}    
    for e in graph.edges():
        policy[e] = True    
    
    for subset in chain.from_iterable(combinations(reqs, r) for r in range(len(reqs)+1)):
        subset = set(subset)
        if len(subset) == 0:
            continue
        
        target = simplify(And([simplify(strToZ3(req[0])) for req in subset] + [simplify(Not(strToZ3(req[0]))) for req in (reqs - set(subset))]))
        print 'target', target
        
        ctl = ['true']
        
        for req in subset:
            ctl = ['and', req[1], ctl]
        
        restrictedGraph = restrictGraph(graph, ctl)
        
        for e in graph.edges():
            if e not in restrictedGraph.edges():
                policy[e] = And(policy[e], Not(target))    
        
        '''        
        propReq = req[0]
        ctlReq = req[1]
        print 'Handling decomposed requirement'
        print 'Q =', propReq
        print 'CTL =', ctlReq
        restrictedGraph = restrictGraph(graph, req)
                
        if restrictedGraph == unsat:
            return unsat        
        for removedEdge in list(set(graph.edges()) - set(restrictedGraph.edges())):
            policy[removedEdge] = simplify(And(policy[removedEdge], Not(strToZ3(propReq))))
       '''
                        
    return policy