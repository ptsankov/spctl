'''
Created on May 2, 2016

@author: ptsankov
'''
import sys
import os
import shutil
from synthesizer import synth
from synthesizer.utils import stats

LOG_DIR = os.path.abspath('casestudies/logs')
NUM_RUNS = 2

def measurePerformance():
    
    configs = {}
    
    configs['Airport'] = os.path.abspath('casestudies/airport/conf')
    configs['Office'] = os.path.abspath('casestudies/office/conf')
    configs['University'] = os.path.abspath('casestudies/university/conf')
    
    if os.path.exists(LOG_DIR):
        shutil.rmtree(LOG_DIR)
    
    os.mkdir(LOG_DIR)
    
    data = {}
    
    for case_study in configs.keys():
        data[case_study] = {}
        data[case_study][stats.SYNTHESIS_TIME] = []
        for i in range(NUM_RUNS):
            stats_map = synth.synth(configs[case_study])
            data[case_study][stats.SYNTHESIS_TIME].append(stats_map[stats.SYNTHESIS_TIME])
            data[case_study][stats.NUMBER_OF_PEPS] = stats_map[stats.NUMBER_OF_PEPS]
            data[case_study][stats.NUMBER_OF_REQUIREMENTS] = stats_map[stats.NUMBER_OF_REQUIREMENTS]
            data[case_study][stats.NUMBER_OF_RESOURCES] = stats_map[stats.NUMBER_OF_RESOURCES]
            
            
    print 'DATAAAA'
    print data