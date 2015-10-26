'''
Created on Aug 11, 2015

@author: ptsankov
'''
from z3 import unsat, Int, If, Not, Or, And, Implies, Solver, ForAll, sat,simplify,\
    Bool, EnumSort
from utils.helperMethods import INIT_RESOURCE, nodePathToEdgePath
from core.solver import encodeFormula
from utils.helperMethods import log
import time
from compiler.ast import Const

TEMPLATE_ENUM_VARS = {}
TEMPLATE_NUMERIC_VARS = {}

ENUM_INDEX = {}
NUM_VAR = Int('time')

BOOL_VARS = {}
ENUM_VARS = {}
ENUM_VALUES = {}
NUMERIC_VARS = {}

def declareAttrVars(subjAttrs):
    for attr in subjAttrs:
        attrName = attr.split(':')[0].strip()
        attrType = attr.split(':')[1].strip()
        if attrType == 'bool':
            BOOL_VARS[attrName] = Bool(attrName)
        elif attrType == 'enum':
            values = attr.split(':')[2].strip().split(',')
            newEnumSort = EnumSort(attrName, values)
            ENUM_VARS[attrName] = Const(attrName, newEnumSort[0])
            ENUM_VALUES[attrName] = {}
            for enumVal in newEnumSort[1]:
                ENUM_VALUES[attrName][str(enumVal)] = enumVal                
        elif attrType == 'numeric':
            print 'numeric type', attrName
            NUMERIC_VARS[attrName] = Int(attrName)
        else:
            raise NameError('unknown attribute type: '+ attrType)

def declareTemplateVars(graph, num_ors, num_enums, num_numeric):
    for enforcementPoint in graph.edges():
        if enforcementPoint not in TEMPLATE_ENUM_VARS.keys():
            TEMPLATE_ENUM_VARS[enforcementPoint] = {}
        if enforcementPoint not in TEMPLATE_NUMERIC_VARS.keys():
            TEMPLATE_NUMERIC_VARS[enforcementPoint] = {}
        if enforcementPoint[0] == enforcementPoint[1]:
            continue
        for or_id in range(num_ors):
            if or_id not in TEMPLATE_ENUM_VARS[enforcementPoint].keys():
                TEMPLATE_ENUM_VARS[enforcementPoint][or_id] = {}
            if or_id not in TEMPLATE_NUMERIC_VARS[enforcementPoint].keys(): 
                TEMPLATE_NUMERIC_VARS[enforcementPoint][or_id] = {}        
            for enum_id in range(num_enums):
                if enum_id not in TEMPLATE_ENUM_VARS[enforcementPoint][or_id].keys(): 
                    TEMPLATE_ENUM_VARS[enforcementPoint][or_id][enum_id] = Int(enforcementPoint[0] + '_' + enforcementPoint[1] + '_or' + str(or_id) + '_enum' + str(enum_id))
            for num_id in range(num_numeric):
                if num_id not in TEMPLATE_NUMERIC_VARS[enforcementPoint][or_id].keys(): 
                    TEMPLATE_NUMERIC_VARS[enforcementPoint][or_id][num_id] = {}
                    TEMPLATE_NUMERIC_VARS[enforcementPoint][or_id][num_id]['min'] = Int(enforcementPoint[0] + '_' + enforcementPoint[1] + '_or' + str(or_id) + '_num' + str(num_id) + '_min')
                    TEMPLATE_NUMERIC_VARS[enforcementPoint][or_id][num_id]['max'] = Int(enforcementPoint[0] + '_' + enforcementPoint[1] + '_or' + str(or_id) + '_num' + str(num_id) + '_max')
                
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

def strToZ3(policy):
    if policy in BOOL_VARS.keys():
        return BOOL_VARS[policy]
    elif policy[0] in ENUM_VARS.keys():
        var = ENUM_VARS[policy[0]] 
        disjunctions = []
        for val in policy[2]:
            disjunctions.append(Or(ENUM_VARS[str(var)] == ENUM_VALUES[str(var)][val]))
        return Or(disjunctions)
    elif policy[0] in NUMERIC_VARS.keys():
        var = NUMERIC_VARS[policy[0]]
        _min = int(policy[2][0])
        _max = int(policy[2][1] )       
        return And(var >= _min, var <= _max)
    elif policy[0] == 'not':
        return Not(strToZ3(policy[1]))
    elif policy[0] == 'and':
        return And([strToZ3(x) for x in policy[1:]])
    elif policy[0] == 'or':
        return Or([strToZ3(x) for x in policy[1:]])
    elif policy[0] == '=>':
        return Implies(strToZ3(policy[1]), strToZ3(policy[2]))
    elif policy == 'true':
        return True
    elif policy == 'false':
        return False
    else:
        raise NameError('could not convert propositional formula to the Z3 format')

def Z3toStr(z3Formula):
    raise NameError('fix the Z3toStr method')
    if z3Formula.decl().name() in BOOL_VARS.keys():
        return z3Formula.decl().name()    
    elif z3Formula.decl().name() == 'not':
        return ['not', Z3toStr(z3Formula.arg(0))]
    elif z3Formula.decl().name() == 'and':
        return ['and'] + [Z3toStr(child) for child in z3Formula.children()]
    elif z3Formula.decl().name() == 'or':
        return ['or'] + [Z3toStr(child) for child in z3Formula.children()]
    elif z3Formula.decl().name() == '=>':
        return ['=>'] + [Z3toStr(child) for child in z3Formula.children()]
    elif z3Formula == True:
        return ['true']
    elif z3Formula == False:
        return ['false']
    else:
        raise NameError('could not convert Z3 formula to string')

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

def policyTemplateForEdge(enforcementPoint, num_ors, num_enums, num_numeric):
    if enforcementPoint[0] == enforcementPoint[1]:
        return True    
    disjunctions = []    
    for or_id in range(num_ors):
        conjunctions = []        
        for enum_id in range(num_enums):                        
            conjunctions.append(enumTemplate(TEMPLATE_ENUM_VARS[enforcementPoint][or_id][enum_id], 0))
        for num_id in range(num_numeric):
            # hardcoding one numeric variable for now!
            minVar = TEMPLATE_NUMERIC_VARS[enforcementPoint][or_id][num_id]['min']
            maxVar = TEMPLATE_NUMERIC_VARS[enforcementPoint][or_id][num_id]['max']
            conjunctions.append(NUM_VAR >= minVar)
            conjunctions.append(NUM_VAR <= maxVar)                                 
        disjunctions.append(And(conjunctions))
    return Or(disjunctions)

def instantiatePolicyTemplateForEdge(enforcementPoint, model, num_ors, num_enums, num_numeric):
    disjunctions = []
    for or_id in range(num_ors):
        conjunctions = []
        for enum_id in range(num_enums):
            enumVar = TEMPLATE_ENUM_VARS[enforcementPoint][or_id][enum_id]
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
        for num_id in range(num_numeric):
            minVar = TEMPLATE_NUMERIC_VARS[enforcementPoint][or_id][num_id]['min']
            if model[minVar] is not None:
                conjunctions.append(NUM_VAR >= model[minVar].as_long())            
            maxVar = TEMPLATE_NUMERIC_VARS[enforcementPoint][or_id][num_id]['max']
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

def synth(resStructure, reqs, subjAttrs):    
    policy = unsat
    numOrs = 1
    numEnums = 0
    numNumeric = 0
    
    declareAttrVars(subjAttrs)
    
    while policy == unsat:
        declareTemplateVars(resStructure, numOrs, numEnums, numNumeric)
        min_size = min(numOrs, numEnums, numNumeric)
        isIncremented = False
        if not isIncremented and numOrs == min_size:
            numOrs += 1
            isIncremented = True
        if not isIncremented and numEnums == min_size:
            numEnums += 1
            isIncremented = True
        if not isIncremented and numNumeric == min_size:
            numNumeric += 1
            isIncremented = True
        policy = solve(resStructure, reqs, subjAttrs, numOrs, numEnums, numNumeric)
                    
    return policy

def synthFixedGrammar(resStructure, reqs, subjAttrs, numOrs, numEnums, numNumeric):
    declareAttrVars(subjAttrs)
    declareTemplateVars(resStructure, numOrs, numEnums, numNumeric)
    return solve(resStructure, reqs, subjAttrs, numOrs, numEnums, numNumeric)    

def solve(resStructure, reqs, subjAttrs, numOrs, numEnums, numNumeric):
    log('Translating requirements to SMT')    
    
        
    start = time.time()
    s = Solver()
    for req in reqs:
        log('Translating requirement' + req)
        reqProp = req[0]
       
        formula = encodeFormula(resStructure, req, INIT_RESOURCE, pathCondition)      
        s.add(ForAll([BOOL_VARS[varName] for varName in BOOL_VARS.keys()] + [ENUM_VARS[varName] for varName in ENUM_VARS.keys()] + [NUM_VAR], Implies(And([strToZ3(reqProp), NUM_VAR >= 0, NUM_VAR <= 24]), formula)))

    timeToTranslate = time.time() - start    
    log('Time for the translation took: ' + str(timeToTranslate))
    
    policy = {}
    
    log('SMT Solving')
    
    start = time.time()
    if s.check() == sat:        
        m = s.model()
        timeToSolve = time.time() - start
        log('Time for the solving: ' + str(timeToSolve))
        for enforcementPoint in resStructure.edges():
            if enforcementPoint[0] == enforcementPoint[1]:
                policy[enforcementPoint] = True
                continue            
            policy[enforcementPoint] = instantiatePolicyTemplateForEdge(enforcementPoint, m) 
        return policy
    else:    
        return unsat
