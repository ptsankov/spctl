'''
Created on Feb 26, 2016

@author: ptsankov
'''

import conf
from z3 import Bool, EnumSort, Int, And, If, Not, Or, simplify
from compiler.ast import Const

BOOL_VARS = {}
ENUM_VARS = {}
ENUM_VALUES = {}
NUMERIC_VARS = {}

ENUM_INDEX = {}

TEMPLATE_ENUM_VARS = {}
TEMPLATE_NUMERIC_VARS = {}

NUM_ORS = -1
NUM_ENUMS = -1
NUM_NUMERIC = -1

NUM_VAR = Int('time')

def declareAttrVars():
    for attr in conf.subjAttrs:
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
            NUMERIC_VARS[attrName] = Int(attrName)
        else:
            raise NameError('unknown attribute type: '+ attrType)

def createTemplate(numOrs, numEnums, numNumeric):
    global NUM_ORS, NUM_ENUMS, NUM_NUMERIC
    
    NUM_ORS = numOrs
    NUM_ENUMS = numEnums
    NUM_NUMERIC = numNumeric
    
    for PEP in conf.PEPS:
        if PEP not in TEMPLATE_ENUM_VARS.keys():
            TEMPLATE_ENUM_VARS[PEP] = {}
        if PEP not in TEMPLATE_NUMERIC_VARS.keys():
            TEMPLATE_NUMERIC_VARS[PEP] = {}        
        for or_id in range(NUM_ORS):
            if or_id not in TEMPLATE_ENUM_VARS[PEP].keys():
                TEMPLATE_ENUM_VARS[PEP][or_id] = {}
            if or_id not in TEMPLATE_NUMERIC_VARS[PEP].keys():
                TEMPLATE_NUMERIC_VARS[PEP][or_id] = {}
            for enum_id in range(NUM_ENUMS):
                if enum_id not in TEMPLATE_ENUM_VARS[PEP][or_id].keys(): 
                    TEMPLATE_ENUM_VARS[PEP][or_id][enum_id] = Int(PEP[0] + '_' + PEP[1] + '_or' + str(or_id) + '_enum' + str(enum_id))
            for num_id in range(NUM_NUMERIC):
                if num_id not in TEMPLATE_NUMERIC_VARS[PEP][or_id].keys(): 
                    TEMPLATE_NUMERIC_VARS[PEP][or_id][num_id] = {}
                    TEMPLATE_NUMERIC_VARS[PEP][or_id][num_id]['min'] = Int(PEP[0] + '_' + PEP[1] + '_or' + str(or_id) + '_num' + str(num_id) + '_min')
                    TEMPLATE_NUMERIC_VARS[PEP][or_id][num_id]['max'] = Int(PEP[0] + '_' + PEP[1] + '_or' + str(or_id) + '_num' + str(num_id) + '_max')
                
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

def PEPTemplate(PEP):
    if PEP not in conf.PEPS:
        return True
    if PEP[0] == PEP[1]:
        return True    
    disjunctions = []    
    for or_id in range(NUM_ORS):
        conjunctions = []        
        for enum_id in range(NUM_ENUMS):                        
            conjunctions.append(enumTemplate(TEMPLATE_ENUM_VARS[PEP][or_id][enum_id], 0))
        for num_id in range(NUM_NUMERIC):
            # hardcoding one numeric variable for now!
            minVar = TEMPLATE_NUMERIC_VARS[PEP][or_id][num_id]['min']
            maxVar = TEMPLATE_NUMERIC_VARS[PEP][or_id][num_id]['max']
            conjunctions.append(NUM_VAR >= minVar)
            conjunctions.append(NUM_VAR <= maxVar)                                 
        disjunctions.append(And(conjunctions))
    return Or(disjunctions)

def PEPPolicy(PEP, model):
    disjunctions = []
    for or_id in range(NUM_ORS):
        conjunctions = []
        for enum_id in range(NUM_ENUMS):
            enumVar = TEMPLATE_ENUM_VARS[PEP][or_id][enum_id]
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
            minVar = TEMPLATE_NUMERIC_VARS[PEP][or_id][num_id]['min']
            if model[minVar] is not None:
                conjunctions.append(NUM_VAR >= model[minVar].as_long())            
            maxVar = TEMPLATE_NUMERIC_VARS[PEP][or_id][num_id]['max']
            if model[maxVar] is not None:
                conjunctions.append(NUM_VAR <= model[maxVar].as_long())
        disjunctions.append(simplify(And(conjunctions)))
    return simplify(Or(disjunctions))