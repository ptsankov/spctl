'''
Created on Aug 12, 2015

@author: ptsankov
'''
from z3 import Solver, Not, And, Or, Implies, sat, unsat
import networkx as nx
import time
import conf
import template
from utils.helperMethods import log

def solve():        
    start = time.time()
    s = Solver()
    for req in conf.reqs:
        print req
        log('Translating requirement: ' + str(req))
        reqProp = req[0]
       
        formula = encode(conf.resourceStructure, req, conf.entryResource)      
        s.add(ForAll([BOOL_VARS[varName] for varName in BOOL_VARS.keys()] + [ENUM_VARS[varName] for varName in ENUM_VARS.keys()] + [NUM_VAR], Implies(And([strToZ3(reqProp), NUM_VAR >= 0, NUM_VAR <= 24]), formula)))

    timeToTranslate = time.time() - start    
    log('DATA| Translation time: ' + str(timeToTranslate))
        
    
    log('SMT Solving')
    
    start = time.time()
    if s.check() == sat:
        policy = {}        
        model = s.model()        
        timeToSolve = time.time() - start
        log('DATA| SMT time: ' + str(timeToSolve))
        for PEP in conf.PEPS:           
            policy[PEP] = template.PEPPolicy(PEP, model) 
        return policy
    else:    
        return unsat


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


def isConstraint(formula):
    if formula[0] == 'not':
        return isConstraint(formula[1])
    elif formula[0] == 'and':
        return isConstraint(formula[1]) and isConstraint(formula[2])
    elif formula[0] == '=>':
        return (not isConstraint(formula[1])) and isConstraint(formula[2])
    elif formula[0] == 'or':
        return (isConstraint(formula[1])) or isConstraint(formula[2])
    else:
        if len(formula) == 3 and formula[1] == 'in':
            return True
        return False

def evalResourceConstraint(graph, resource, constraint):
    if constraint[0] == 'not':
        return not evalResourceConstraint(graph, resource, constraint[1])
    elif constraint[0] == 'and':
        return evalResourceConstraint(graph, resource, constraint[1]) and evalResourceConstraint(graph, resource, constraint[2])
    elif constraint[0] == '=>':
        return (not evalResourceConstraint(graph, resource, constraint[1])) and evalResourceConstraint(graph, resource, constraint[2])
    elif constraint[0] == 'or':
        return evalResourceConstraint(graph, resource, constraint[1]) or evalResourceConstraint(graph, resource, constraint[2])
    else:
        assert isConstraint(constraint)
        attrName = constraint[0]
        attrVals = constraint[2]
        attrVal = graph.node[resource][attrName]
        return any(attrVal == x for x in attrVals)        

def encode(graph, req, resource, pathConditionFunction):
    reqProp = req[0]
    reqCTL = req[1]
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
        subFormula = encode(graph, [reqProp, reqCTL[1]], resource, pathConditionFunction)
        return Not(subFormula)
    elif any(reqCTL[0] == x for x in ['and', 'or', '=>']):
        subFormulaLeft = encode(graph, [reqProp, reqCTL[1]], resource, pathConditionFunction)
        subFormulaRight = encode(graph, [reqProp, reqCTL[2]], resource, pathConditionFunction)
        if reqCTL[0] == 'and':
            return And(subFormulaLeft, subFormulaRight)
        elif reqCTL[0] == 'or':
            return Or(subFormulaLeft, subFormulaRight)
        elif reqCTL[0] == '=>':
            return Implies(subFormulaLeft, subFormulaRight)
    elif reqCTL[0] == 'EF':                            
        if isConstraint(reqCTL[1]):    
            pathDisjuncts = []
            for targetResource in graph.nodes():
                if evalResourceConstraint(graph, targetResource, reqCTL[1]) == False:
                    continue
                for path in nx.all_simple_paths(graph, resource, targetResource):
                    pathCondition = pathConditionFunction(graph, path, req)
                    pathDisjuncts.append(pathCondition)
            return Or(pathDisjuncts)
        else:
            raise NameError('TODO: Add support for path quantifiers in EF')
    elif reqCTL[0] == 'EU':
        targetResources = graph.nodes()
        if reqCTL[2] in graph.nodes():
            targetResources = [reqCTL[2]]
        disjuncts = []
        for targetResource in targetResources:
            for path in nx.all_simple_paths(graph, resource, targetResource):
                for i in range(len(path)):
                    conjuncts = []                    
                    subpath = path[0:i+1]
                    pathCondition = pathConditionFunction(graph, subpath, req)           
                    conjuncts.append(pathCondition)
                    conjuncts.append(encode(graph, [reqProp, reqCTL[2]], path[i], pathConditionFunction))
                    for j in range(0, i):
                        conjuncts.append(encode(graph, [reqProp, reqCTL[1]], path[j], pathConditionFunction))                                        
                    s = Solver()
                    s.add(And(conjuncts))
                    # add only if the condition is feasible
                    if s.check() == sat:                                        
                        disjuncts.append(And(conjuncts))
        return Or(disjuncts)
    elif reqCTL[0] == 'AG':
        conjuncts = []        
        for targetResource in graph.nodes():
            if reqCTL[1][0] == '=>' and isConstraint(reqCTL[1][1]):               
                if not evalResourceConstraint(graph, targetResource, reqCTL[1][1]):
                    continue            
            subFormula = encode(graph, [reqProp, reqCTL[1]], targetResource, pathConditionFunction)
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
        # it must be an atomic constraint
        #print reqCTL
        assert isConstraint(reqCTL)
        attrName = reqCTL[0]
        attrVals = reqCTL[2]
        attrVal = graph.node[resource][attrName]
        return any(attrVal == x for x in attrVals)

