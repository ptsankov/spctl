#!/bin/python

import sys
import networkx as nx

G = None
A = ['visitor', 'owner']

def initGraph():
    global G
    G = nx.DiGraph()
    G.add_nodes_from(['out', 'lob', 'cor', 'off', 'mr'])
    G.add_edges_from([('out', 'lob'), ('out', 'cor')])
    G.add_edges_from([('lob', 'out'), ('lob', 'cor')])
    G.add_edges_from([('cor', 'lob'), ('cor', 'out'), ('cor', 'off'), ('cor', 'mr')])
    G.add_edge('off', 'cor')
    G.add_edge('mr', 'cor')

def parseZ3File(inputFile):    
    lines = [line.strip() for line in open(inputFile)]
    for e in G.edges():
        left = None
        right = None
        op = None
        i = 0
        while i < len(lines):
            if '(define-fun {}_{}_h0 () Int'.format(e[0], e[1]) in lines[i]:
                synthOp = lines[i+1].split(')')[0]
                if int(synthOp) == 0:
                    op = '&'
                else:
                    op = '|'
            if '(define-fun {}_{}_h1 () Int'.format(e[0], e[1]) in lines[i]:
                synthLeft = lines[i+1].split(')')[0]
                if int(synthLeft) == 0:
                    left = 'owner'
                elif int(synthLeft) == 1:
                    left = '!owner'
                else:
                    left = 'TRUE'
            if '(define-fun {}_{}_h2 () Int'.format(e[0], e[1]) in lines[i]:
                synthRight = lines[i+1].split(')')[0]
                if int(synthRight) == 0:
                    right = 'visitor'
                elif int(synthRight) == 1:
                    right = '!visitor'
                else:
                    right = 'TRUE'
            i += 1
        print 'authz_{}_{} := {} {} {};'.format(e[0], e[1], left, op, right)

def main(argv):    
    inputFile = argv[0]
    print 'Deriving authorizations from Z3 output:', inputFile
    parseZ3File(inputFile)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print 'Usage:', sys.argv[0], '<smv plan file>'
        sys.exit()
    
    initGraph()
    
    main(sys.argv[1:])
