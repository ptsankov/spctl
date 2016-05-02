'''
Created on May 2, 2016

@author: ptsankov
'''

translation_time = 0
smt_time = 0

def resetTimers():
    global translation_time, smt_time
    translation_time = 0
    smt_time = 0

def addToTranslationTime(t):
    global translation_time
    translation_time += t
    
def addToSMTTime(t):
    global smt_time
    smt_time += t