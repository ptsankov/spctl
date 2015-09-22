'''
Created on Aug 11, 2015

@author: ptsankov
'''
from z3 import unsat, Int, If, Not, Or, And, Implies, Solver, ForAll, sat,simplify
from utils.helperMethods import INIT_RESOURCE, strToZ3, BOOL_VARS, ENUM_VALUES,\
    ENUM_VARS
from ctl.ctl_solver import nodePathToEdgePath, encodeFormula
import time

NUM_ORS = 1
NUM_ENUMS = 1
NUM_NUMERIC = 1

TEMPLATE_ENUM_VARS = {}
TEMPLATE_NUMERIC_VARS = {}

ENUM_INDEX = {}

NUM_VAR = Int('time')

def declareTemplateVars(attrs, graph):
    global ENUM_RANGE    
    
    for edge in graph.edges():
        TEMPLATE_ENUM_VARS[edge] = {}
        TEMPLATE_NUMERIC_VARS[edge] = {}
        if edge[0] == edge[1]:
            continue
        for or_id in range(NUM_ORS):
            TEMPLATE_ENUM_VARS[edge][or_id] = {}
            TEMPLATE_NUMERIC_VARS[edge][or_id] = {}        
            for enum_id in range(NUM_ENUMS):
                TEMPLATE_ENUM_VARS[edge][or_id][enum_id] = Int(edge[0] + '_' + edge[1] + '_or' + str(or_id) + '_enum' + str(enum_id))
            for num_id in range(NUM_NUMERIC):
                TEMPLATE_NUMERIC_VARS[edge][or_id][num_id] = {}
                TEMPLATE_NUMERIC_VARS[edge][or_id][num_id]['min'] = Int(edge[0] + '_' + edge[1] + '_or' + str(or_id) + '_num' + str(num_id) + '_min')
                TEMPLATE_NUMERIC_VARS[edge][or_id][num_id]['max'] = Int(edge[0] + '_' + edge[1] + '_or' + str(or_id) + '_num' + str(num_id) + '_max')
                
    index = 0
    for boolVarName in BOOL_VARS.keys():
        ENUM_INDEX[index] = BOOL_VARS[boolVarName]                
        index += 1
    for enumVarName in ENUM_VARS.keys():
        enumVar = ENUM_VARS[enumVarName]
        for valName in ENUM_VALUES[enumVarName].keys():
            val = ENUM_VALUES[enumVarName][valName]
            ENUM_INDEX[index] = [enumVar, val]
            index += 1

def enumTemplate(enumTempVar, index):
    if index < len(ENUM_INDEX.keys()):
        if not isinstance(ENUM_INDEX[index], list):
            boolVar = ENUM_INDEX[index]
            return If(enumTempVar == index, boolVar, enumTemplate(enumTempVar, index+1))
        else:
            [enumVar, val] = ENUM_INDEX[index]
            return If(enumTempVar == index, enumVar == val, enumTemplate(enumTempVar, index+1))
    elif index >= len(ENUM_INDEX.keys()) and index < 2*len(ENUM_INDEX.keys()):
        if not isinstance(ENUM_INDEX[index - len(ENUM_INDEX)], list):
            boolVar = ENUM_INDEX[index - len(ENUM_INDEX)]
            return If(enumTempVar == index, Not(boolVar), enumTemplate(enumTempVar, index+1))
        else:
            [enumVar, val] = ENUM_INDEX[index - len(ENUM_INDEX)]
            return If(enumTempVar == index, enumVar != val, enumTemplate(enumTempVar, index+1))
    elif index == 2 * len(ENUM_INDEX.keys()):
        return If(enumTempVar == index, True, False)
    else:
        raise NameError('not reachable')

def numTemplate(minVar, maxVar):
    return And(NUM_VAR >= minVar, NUM_VAR <= maxVar)

def policyTemplateForEdge(edge):
    if edge[0] == edge[1]:
        return True    
    disjunctions = []    
    for or_id in range(NUM_ORS):
        conjunctions = []        
        for enum_id in range(NUM_ENUMS):                        
            conjunctions.append(enumTemplate(TEMPLATE_ENUM_VARS[edge][or_id][enum_id], 0))
        for num_id in range(NUM_NUMERIC):
            # hardcoding one numeric variable for now!
            minVar = TEMPLATE_NUMERIC_VARS[edge][or_id][num_id]['min']
            maxVar = TEMPLATE_NUMERIC_VARS[edge][or_id][num_id]['max']
            conjunctions.append(NUM_VAR >= minVar)
            conjunctions.append(NUM_VAR <= maxVar)                                 
        disjunctions.append(And(conjunctions))
    return Or(disjunctions)

def instantiatePolicyTemplateForEdge(edge, model):
    disjunctions = []
    for or_id in range(NUM_ORS):
        conjunctions = []
        for enum_id in range(NUM_ENUMS):
            enumVar = TEMPLATE_ENUM_VARS[edge][or_id][enum_id]
            if model[enumVar] is not None:
                synthVal = model[enumVar].as_long()
            else:
                synthVal = -1
            if synthVal >= 0 and synthVal < len(ENUM_INDEX.keys()):                
                if not isinstance(ENUM_INDEX[synthVal], list):
                    boolVar = ENUM_INDEX[synthVal]
                    conjunctions.append(boolVar)
                else:
                    [enumVar, val] = ENUM_INDEX[synthVal]
                    conjunctions.append(enumVar == val)
            elif synthVal >= len(ENUM_INDEX.keys()) and synthVal < 2 * len(ENUM_INDEX.keys()):                
                if not isinstance(ENUM_INDEX[synthVal - len(ENUM_INDEX.keys())], list):
                    boolVar = ENUM_INDEX[synthVal - len(ENUM_INDEX.keys())]
                    conjunctions.append(Not(boolVar))
                else:
                    [enumVar, val] = ENUM_INDEX[synthVal - len(ENUM_INDEX.keys())]
                    conjunctions.append(enumVar != val)
            elif synthVal == 2 * len(ENUM_INDEX.keys()):
                conjunctions.append(True)
            else:
                conjunctions.append(False)
        for num_id in range(NUM_NUMERIC):
            minVar = TEMPLATE_NUMERIC_VARS[edge][or_id][num_id]['min']
            if model[minVar] is not None:
                conjunctions.append(NUM_VAR >= model[minVar].as_long())            
            maxVar = TEMPLATE_NUMERIC_VARS[edge][or_id][num_id]['max']
            if model[maxVar] is not None:
                conjunctions.append(NUM_VAR <= model[maxVar].as_long())
        disjunctions.append(simplify(And(conjunctions)))
    return simplify(Or(disjunctions))
            
def pathCondition(graph, path, req):
    if len(path) < 2:
        return True
    if path[0] == path[-1]:
        return True
    reqProp = req[0]
    edgePath = nodePathToEdgePath(graph, path)
    edgeTemplates = [policyTemplateForEdge(e) for e in edgePath]   
    cond = Implies(strToZ3(reqProp), And(edgeTemplates))
    return cond
    
    

def synth(graph, reqs, attrs):
    print 'Running the policy synthesis algorithm'
    
    declareTemplateVars(attrs, graph)
    
    
    start = time.time()
    s = Solver()
    for req in reqs:
        reqProp = req[0]
        reqCTL = req[1]
        print 'Q =', reqProp
        print 'CTL =', reqCTL
        
        formula = encodeFormula(graph, req, INIT_RESOURCE, pathCondition)
        #s.add(ForAll([BOOL_VARS[varName] for varName in BOOL_VARS.keys()] + [ENUM_VARS[varName] for varName in ENUM_VARS.keys()] + [NUM_VAR], Implies(And([strToZ3(reqProp), NUM_VAR >= 0, NUM_VAR <= 24]), formula)))        
        s.add(ForAll([BOOL_VARS[varName] for varName in BOOL_VARS.keys()] + [ENUM_VARS[varName] for varName in ENUM_VARS.keys()] + [NUM_VAR], Implies(And([strToZ3(reqProp), NUM_VAR >= 0, NUM_VAR <= 24]), formula)))


#    for e in graph.edges():
#        print 'policy template for edge', e
#        print '-----------------------------------------------------------------------'
#        print policyTemplateForEdge(e)    
#        print '-----------------------------------------------------------------------'
    timeToTranslate = time.time() - start    
    print 'Time for the translation took: ' + str(timeToTranslate)
    
    policy = {}
    start = time.time()
    if s.check() == sat:        
        m = s.model()
        timeToSolve = time.time() - start
        print 'Time for the solving: ' + str(timeToSolve)
        for edge in graph.edges():
            if edge[0] == edge[1]:
                policy[edge] = True
                continue            
            policy[edge] = instantiatePolicyTemplateForEdge(edge, m) 
        return policy
    else:    
        return unsat
