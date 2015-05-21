from utils import write

NUM_ORS = 3
NUM_ANDS = 3

TRUE_ID = -1

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
            
    write('(define-fun from_to_hole ((from Room) (to Room) (i Int)) Int\n')
    for edge in resGraph.edges():
        for i in range(NUM_ORS * NUM_ANDS): 
            write('  (if (and (= from {}) (= to {}) (= i {})) {}_{}_hole{}\n'.format(edge[0], edge[1], str(i), edge[0], edge[1], str(i)))
    write('  -1')
    for edge in resGraph.edges():
        for i in range(NUM_ORS * NUM_ANDS):
            write(')')
    write(')\n')    
    
    write('(define-fun hole ((i Int) {}) Bool\n'.format(' '.join(['(' + attr + ' Bool)' for attr in attrs])))
    write('  (if (= i {}) true\n'.format(str(TRUE_ID)))
    for i in range(len(attrs)):
        write('  (if (= i {}) {}\n'.format(str(i), attrs[i]))
    for i in range(len(attrs)):
        write('  (if (= i {}) (not {})\n'.format(str(i + len(attrs)), attrs[i]))
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
    write('  )\n')
    write(')\n')
    
def declareCTLMustHold(ctlFuncNames, attrs):
    write('(assert\n')
    write('  (forall ({})\n'.format(' '.join(['(room0 Bool)'] + ['(' + attr + ' Bool)' for attr in attrs])))
    write('    (and\n')
    
    for ctlFunc in ctlFuncNames:
        write('        ({} room0 {})\n'.format(ctlFunc, ' '.join(attrs)))
    write('    )\n')
    write('  )\n')
    write(')\n')