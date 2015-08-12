'''
Created on Aug 11, 2015

@author: ptsankov
'''
from z3 import unsat, Int, If, Not, Or, And
from utils.helperMethods import ATTR_VARS

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
        return True

def policyTemplate(edge):    
    conjunctions = []    
    for i in range(NUM_ANDS):
        disjunctions = []        
        for j in range(NUM_ORS):            
            pos = i * NUM_ANDS + j
            disjunctions.append(attrTemplate(TEMPLATE_VARS[edge, pos], 0))
        conjunctions.append(Or(disjunctions))
    return And(conjunctions)
            
            

def policyGuidedSynth(graph, reqs, attrs):
    print 'Running the policy-guided synthesis algorithm'
    
    declareTemplateVars(attrs, graph)
    
    for edge in graph.edges():
        if edge[0] == edge[1]:
            continue
        print 'edge', edge, 'template', policyTemplate(edge)
    
    return unsat