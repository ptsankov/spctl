'''
Created on Aug 11, 2015

@author: ptsankov
'''
from z3 import unsat, Int, If, Not, Or, And, Implies, Solver, ForAll, sat
from utils.helperMethods import ATTR_VARS, INIT_RESOURCE, strToZ3
from ctl.ctl_solver import nodePathToEdgePath, encodeFormula

NUM_ORS = 2
NUM_ANDS = 2

TEMPLATE_VARS = {}

def declareTemplateVars(attrs, graph):    
    for edge in graph.edges():
        if edge[0] == edge[1]:
            continue
        for position in range(NUM_ORS * NUM_ANDS):
            TEMPLATE_VARS[edge, position] = Int(edge[0] + '_' + edge[1] + '_' + str(position))

def attrTemplate(templateIntVar, index):
    numAttrs = len(ATTR_VARS.keys())
    if index in range(numAttrs):
        attr = ATTR_VARS.keys()[index]
        return If(templateIntVar == index, ATTR_VARS[attr], attrTemplate(templateIntVar, index+1))
    elif index in range(numAttrs, numAttrs*2):
        attr = ATTR_VARS.keys()[index - numAttrs]
        return If(templateIntVar == index, Not(ATTR_VARS[attr]), attrTemplate(templateIntVar, index+1))
    else:
        return False

def policyTemplate(edge):    
    conjunctions = []    
    for i in range(NUM_ANDS):
        disjunctions = []        
        for j in range(NUM_ORS):            
            pos = i * NUM_ANDS + j
            disjunctions.append(attrTemplate(TEMPLATE_VARS[edge, pos], 0))
        conjunctions.append(Or(disjunctions))
    return And(conjunctions)
            
def policyGuidedPathCondition(graph, path, req):
    print 'path condition for', path
    if len(path) < 2:
        return True
    reqProp = req[0]
    edgePath = nodePathToEdgePath(graph, path)    
    edgeTemplates = [policyTemplate(e) for e in edgePath]   
    pathCondition = Implies(strToZ3(reqProp), And(edgeTemplates))
    return pathCondition
    
    

def policyGuidedSynth(graph, reqs, attrs):
    print 'Running the policy-guided synthesis algorithm'
    
    declareTemplateVars(attrs, graph)
    
    s = Solver()
    for req in reqs:
        reqProp = req[0]
        reqCTL = req[1]
        print 'Q =', reqProp
        print 'CTL =', reqCTL
        
        formula = encodeFormula(graph, req, INIT_RESOURCE, policyGuidedPathCondition)
        s.add(ForAll([ATTR_VARS[attr] for attr in ATTR_VARS.keys()], Implies(strToZ3(reqProp), formula)))        
    
    if s.check() == sat:
        print s.model()
    else:    
        return unsat