from utils import write

def declareRooms(resGraph, outFile):
    write('(declare-sort Room)\n')
    for res in resGraph.nodes():
        write('(declare-const {} Room)\n'.format(res))
    write('(assert (distinct {}))\n'.format(' '.join(resGraph.nodes())))
    write('(assert (forall ((r Room)) (or ' + ' '.join(['(= r ' + x + ')' for x in resGraph.nodes()]) + ')))\n')
    