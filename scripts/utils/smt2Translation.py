from utils import write

NUM_ORS = 3
NUM_ANDS = 3

def declareRooms(resGraph):
    write('(declare-sort Room)\n')
    for res in resGraph.nodes():
        write('(declare-const {} Room)\n'.format(res))
    write('(assert (distinct {}))\n'.format(' '.join(resGraph.nodes())))
    write('(assert (forall ((r Room)) (or ' + ' '.join(['(= r ' + x + ')' for x in resGraph.nodes()]) + ')))\n')
    
    
def declarePolicyTemplates(resGraph):
    for edge in resGraph.edges():
        for i in range(NUM_ORS * NUM_ANDS):
            write('(declare-const {}_{}_hole{} Int)\n'.format(edge[0], edge[1], str(i)))
    
    write('(define-fun authz ((from Room) (to Room) (o Bool) (v Bool)) Bool\n')
    write(')')