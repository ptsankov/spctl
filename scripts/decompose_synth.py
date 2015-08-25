'''
Created on Aug 11, 2015

@author: ptsankov
'''
from z3 import Solver, Not, And, sat, simplify, unsat, Bool
from ctl import ctl_grammar
from ctl.ctl_solver import restrictGraph
from utils.helperMethods import strToZ3, EDGE_VARS, setEdgeVars, Z3toStr

  
    
# decouple requirements into
# (Q1, F1), ..., (Qn, Fn) such that for all i, j we have (Qi and Qj = False)
def decomposeReqs(reqs):
    curReqs = []
    curReqs.append(reqs.pop())
    
    s = Solver()    
    
    #print '======================== INITIAL STEP ========================'
    #for r in curReqs:
    #    print '========================'
    #    print 'q = ', r[0]
    #    print 'ctl = ', r[1]
    
    for req in reqs:
        
        #print '===========TAKING FROMT THE QUEUE============='
        #print 'q = ', req[0]
        #print 'ctl = ', req[1]
        
        nextReqs = []
        depReqs = []
        for curReq in curReqs:
            s.reset()
            s.add(And(strToZ3(curReq[0]), strToZ3(req[0])))
            if s.check() == sat:
                # the two requirements overlap
                depReqs.append(curReq)
            else:
                # the requirements are independent
                nextReqs.append(curReq)
                
        for depReq in depReqs:
            # Case (Q and Qi, F and Fi)
            depProp = strToZ3(depReq[0])
            reqProp =  strToZ3(req[0])
            
            s.reset()
            s.add(And(depProp, reqProp))
            if s.check() == sat:
                newReqProp = Z3toStr(simplify(And(depProp, reqProp)))                
                newReqCTL = ['and', depReq[1], req[1]]
                #print 'depReq[1]', depReq[1]
                #print 'req[1]', req[1]
                #print 'newReqCTL', ['and', depReq[1], req[1]]

                newReq = [newReqProp, newReqCTL]
                nextReqs.append(newReq)
            
            # Case (not Q and Qi, not F and Fi)
            s.reset()
            s.add(And(depProp, Not(reqProp)))
            if s.check() == sat:
                newReqProp = Z3toStr(simplify(And(depProp, Not(reqProp))))
                newReqCTL = depReq[1]
                #print 'depReq[1]', depReq[1]
                #print 'newReqCTL', depReq[1]
                newReq = [newReqProp, newReqCTL]
                nextReqs.append(newReq)
        
        # Case (Q and not Q1 and ... and not Qn, F and not F1 and ... not Fn)
        tmp = simplify(And([Not(strToZ3(depReq[0])) for depReq in depReqs]))
        reqProp =  strToZ3(req[0])
        s.reset()
        s.add(And(reqProp, tmp))
        if s.check() == sat:
            newReqProp = Z3toStr(simplify(And(reqProp, tmp)))                
            newReqCTL = req[1]
            #print 'req[1]', req[1]
            #print 'newReqCTL', req[1]
            newReq = [newReqProp, newReqCTL]
            nextReqs.append(newReq)    
        
        curReqs = nextReqs
        
        #print '======================== NEXT STEP ========================'
        #for r in curReqs:
        #    print '========================'
        #    print 'q = ', r[0]
        #    print 'ctl = ', r[1]
        
    return curReqs

def synth(graph, reqs):
    print 'Running the decompose synthesis algorithm'    
    setEdgeVars(graph)
        
    decomposedReqs = decomposeReqs(reqs)
    print 'FINAL DECOMPOSED REQUIREMNETS'
    for r in decomposedReqs:
        print '========================'
        print 'q = ', r[0]
        print 'ctl = ', r[1]
        
    
    policy = {}
    for edge in graph.edges():
        policy[edge] = True        
           
    for req in decomposedReqs:
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
       
    return policy