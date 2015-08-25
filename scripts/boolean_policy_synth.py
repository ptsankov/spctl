'''
Created on Aug 11, 2015

@author: ptsankov
'''
from z3 import unsat, Int, If, Not, Or, And, Implies, Solver, ForAll, sat,simplify
from utils.helperMethods import ATTR_VARS, INIT_RESOURCE, strToZ3
from ctl.ctl_solver import nodePathToEdgePath, encodeFormula

NUM_ORS = 3
NUM_ANDS = 3

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
        return True

def policyTemplateForEdge(edge):
    if edge[0] == edge[1]:
        return True    
    conjunctions = []    
    for i in range(NUM_ANDS):
        disjunctions = []        
        for j in range(NUM_ORS):            
            pos = i * NUM_ANDS + j
            disjunctions.append(attrTemplate(TEMPLATE_VARS[edge, pos], 0))
        conjunctions.append(Or(disjunctions))
    return And(conjunctions)

def instantiatePolicyTemplateForEdge(edge, model):
    numAttrs = len(ATTR_VARS.keys())
    conjunctions = []
    for i in range(NUM_ANDS):
        disjunctions = []
        for j in range(NUM_ORS):
            pos = i * NUM_ANDS + j
            if model[TEMPLATE_VARS[edge, pos]] is not None:
                synthVal = model[TEMPLATE_VARS[edge, pos]].as_long()
            else:
                synthVal = -1
            attr = ATTR_VARS.keys()[synthVal % numAttrs]
            if synthVal in range(numAttrs):
                disjunctions.append(ATTR_VARS[attr])
            elif synthVal in range(numAttrs, numAttrs*2):
                disjunctions.append(Not(ATTR_VARS[attr]))
            else:
                disjunctions.append(True)
        conjunctions.append(simplify(Or(disjunctions)))
    return simplify(And(conjunctions))
            
def pathCondition(graph, path, req):
    if len(path) < 2:
        return True
    reqProp = req[0]
    edgePath = nodePathToEdgePath(graph, path)  
    edgeTemplates = [policyTemplateForEdge(e) for e in edgePath]   
    pathCondition = Implies(strToZ3(reqProp), And(edgeTemplates))
    return pathCondition
    
    

def synth(graph, reqs, attrs):
    print 'Running the boolean policy synthesis algorithm'
    
    declareTemplateVars(attrs, graph)
    
    s = Solver()
    for req in reqs:
        reqProp = req[0]
        reqCTL = req[1]
        print 'Q =', reqProp
        print 'CTL =', reqCTL
        
        formula = encodeFormula(graph, req, INIT_RESOURCE, pathCondition)
        s.add(ForAll([ATTR_VARS[attr] for attr in ATTR_VARS.keys()], Implies(strToZ3(reqProp), formula)))        
    
    
    policy = {}
    
    if s.check() == sat:
        m = s.model()
        print m
        for edge in graph.edges():
            if edge[0] == edge[1]:
                policy[edge] = True
                continue
            policy[edge] = instantiatePolicyTemplateForEdge(edge, m)
        return policy
    else:    
        return unsat
