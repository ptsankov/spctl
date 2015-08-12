'''
Author: ptsankov
'''

from utils import write
from z3 import Int, Bool, And, Or, simplify, Not


NUM_ORS = 2
NUM_ANDS = 2

def declareRooms(resGraph):
    write('(declare-sort Room)\n')
    for res in resGraph.nodes():
        write('(declare-const {} Room)\n'.format(res))
    write('(assert (distinct {}))\n'.format(' '.join(resGraph.nodes())))
    write('(assert (forall ((r Room)) (or ' + ' '.join(['(= r ' + x + ')' for x in resGraph.nodes()]) + ')))\n')    
    
def declarePolicyTemplates(resGraph, attrs):
    for edge in resGraph.edges():
        for i in range(NUM_ORS * NUM_ANDS):
            write('(declare-const {}_{}_hole{} Int)\n'.format(edge[0], edge[1], str(i)))
            #write('(assert (>= {}_{}_hole{} 0))\n'.format(edge[0], edge[1], str(i)))
            #write('(assert (<= {}_{}_hole{} {}))\n'.format(edge[0], edge[1], str(i), str(2 * len(attrs) + 2)))
            
    write('(define-fun from_to_hole ((from Room) (to Room) (i Int)) Int\n')
    for edge in resGraph.edges():
        for i in range(NUM_ORS * NUM_ANDS): 
            write('  (if (and (= from {}) (= to {}) (= i {})) {}_{}_hole{}\n'.format(edge[0], edge[1], str(i), edge[0], edge[1], str(i)))
    write('  {}'.format(2 * len(attrs) + 1))
    for edge in resGraph.edges():
        for i in range(NUM_ORS * NUM_ANDS):
            write(')')
    write(')\n')    
    
    write('(define-fun hole ((i Int) {}) Bool\n'.format(' '.join(['(' + attr + ' Bool)' for attr in attrs])))
    #write('  (if (= i {}) true\n'.format(str(TRUE_ID)))    
    for i in range(len(attrs)):
        write('  (if (= i {}) {}\n'.format(str(i), attrs[i]))
    for i in range(len(attrs)):
        write('  (if (= i {}) (not {})\n'.format(str(i + len(attrs)), attrs[i]))
    write('  (if (= i {}) true\n'.format(len(attrs)*2))
    write('  false')
    for i in range(len(attrs)*2+1):
        write(')')    
    write(')\n')
    
    write('(define-fun authz ((from Room) (to Room) {}) Bool\n'.format(' '.join(['(' + attr + ' Bool)' for attr in attrs])))
    write('  (or\n')
    for i in range(NUM_ORS):
        write('    (and\n')        
        for j in range(NUM_ANDS):
            write('      (hole (from_to_hole from to {}) {})\n'.format(str(i*NUM_ANDS + j), ' '.join(attrs)))
        write('    )\n')
    write('    (= from to)\n')
    write('  )\n')
    write(')\n')
    
def declareCTLMustHold(ctlFuncNames, attrs):
    write('(assert\n')
    #write('  (forall ({})\n'.format(' '.join(['(room0 Room)'] + ['(' + attr + ' Bool)' for attr in attrs])))
    write('  (forall ({})\n'.format(' '.join(['(' + attr + ' Bool)' for attr in attrs])))
    write('    (and\n')
    
    for ctlFunc in ctlFuncNames:
        #write('        ({} room0 {})\n'.format(ctlFunc, ' '.join(attrs)))
        write('        ({} {})\n'.format(ctlFunc, ' '.join(attrs)))
    write('    )\n')
    write('  )\n')
    write(')\n')
    #write('(check-sat)\n')
    #write('(get-model)')
    
def modelToPolicy(model, resGraph, attrs):
    for edge in resGraph.edges():
        print 'authz_{}_{} := '.format(edge[0], edge[1]),
        disjuncts = []
        for i in range(NUM_ORS):
            conjuncts = []
            for j in range(NUM_ANDS):
                hole = model[Int('{}_{}_hole{}'.format(edge[0], edge[1], i*NUM_ANDS + j))].as_long()
                if hole >= 0 and hole < len(attrs):                    
                    conjuncts.append(attrs[hole])
                elif hole >= len(attrs) and hole < 2 * len(attrs):
                    conjuncts.append('!' + attrs[hole - len(attrs)])
                elif hole == 2 * len(attrs):
                    conjuncts.append('TRUE')
                else:
                    conjuncts.append('FALSE')
            disjuncts.append('(' + ' & '.join(conjuncts) + ')')
        print ' | '.join(disjuncts)
                
def modelToSimplifiedPolicy(model, resGraph, attrs):
    for edge in resGraph.edges():
        print 'authz_{}_{} := '.format(edge[0], edge[1]),
        disjuncts = []
        for i in range(NUM_ORS):
            conjuncts = []
            for j in range(NUM_ANDS):
                hole = model[Int('{}_{}_hole{}'.format(edge[0], edge[1], i*NUM_ANDS + j))].as_long()
                if hole >= 0 and hole < len(attrs):
                    conjuncts.append(Bool(attrs[hole]))
                elif hole >= len(attrs) and hole < 2 * len(attrs):
                    conjuncts.append(Not(Bool(attrs[hole - len(attrs)])))
                elif hole == 2 * len(attrs):
                    conjuncts.append(True)
                else:
                    conjuncts.append(False)
            disjuncts.append(And(conjuncts))
        policy = simplify(Or(disjuncts))
        print policy
