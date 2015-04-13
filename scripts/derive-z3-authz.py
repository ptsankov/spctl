#!/bin/python

import sys
import networkx as nx
import itertools

G = None
A = ['visitor', 'owner']
#A = ['visitor', 'owner', 'owner_delegate', 'owner_cond_delegate']
Authz = {} # authorizations
attrPerms = None

def setAttrs(attrs, vals):
    if len(attrs) == 0:
        return {}
    rest = setAttrs(attrs[1:], vals[1:])
    rest[attrs[0]] = vals[0]
    return rest

def getAttrPerms():
    global attrPerms
    attrPerms = genAttrCombinations() # Attribute permutations

def genAttrCombinations():
    attrs = []
    for vals in itertools.product([False, True], repeat=len(A)):
        attrs.append(setAttrs(A, vals))
    return attrs

def attrPermToStr(attrPerm):
    strList = []
    for attr in A:
        if attrPerm[attr]:
            strList.append(attr)
        else:
            strList.append('!' + attr)
    return ' & '.join(strList)

def initGraph():
    global G
    G = nx.DiGraph()
    G.add_nodes_from(['out', 'lob', 'cor', 'off', 'mr'])
    G.add_edges_from([('out', 'lob'), ('out', 'cor')])
    G.add_edges_from([('lob', 'out'), ('lob', 'cor')])
    G.add_edges_from([('cor', 'lob'), ('cor', 'out'), ('cor', 'off'), ('cor', 'mr')])
    G.add_edge('off', 'cor')
    G.add_edge('mr', 'cor')

def getZ3Expression(req, attrPerm):
    return '(define-fun authz_{}_{}_{}'.format(req, 'o' if attrPerm['owner'] else 'noto', 'v' if attrPerm['visitor'] else 'notv')

def parseZ3File(planFile):
    global Authz
    lines = [line.strip() for line in open(planFile)]
    for edge in G.edges():
        req = edge[0] + '_' + edge[1]
        Authz[req] = []
        for attrPerm in attrPerms:    
            print attrPerm          
            i = 0
            while i < len(lines):
                line = lines[i]
                exprToMatch = getZ3Expression(req, attrPerm)
                if exprToMatch in line:
                    if 'true' in lines[i+1] and attrPermToStr(attrPerm) not in Authz[req]:
                        Authz[req].append(attrPermToStr(attrPerm))
                i += 1

def outputAuthz():
    print '------ DERIVED AUTHORIZATIONS --------'
    print 'DEFINE'
    for edge in G.edges():
        req = edge[0] + '_' + edge[1]
        if len(Authz[req]) != 0:
            print '  authz_' + req + ' := ' + ' | '.join(['(' + x + ')' for x in Authz[req]]) + ';'
        else:
            print '  authz_' + req + ' := FALSE;'
    print '------ END --------'

def main(argv):    
    planFile = argv[0]
    print 'Deriving authorizations from SMV plan file:', planFile
    parseZ3File(planFile)
    print Authz
    outputAuthz()

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print 'Usage:', sys.argv[0], '<smv plan file>'
        sys.exit()
    
    initGraph()
    getAttrPerms()
    
    main(sys.argv[1:])
