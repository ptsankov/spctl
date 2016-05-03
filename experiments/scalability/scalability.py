'''
Created on May 3, 2016

@author: ptsankov
'''
import os
import shutil
from synthesizer.utils import stats
from synthesizer import synth

MIN_SIZE = 1
MAX_SIZE = 30

LOG_DIR = os.path.abspath('experiments/scalability/logs')
START_RUN = 1
NUM_RUNS = 1

def measure_scalability():
    
    if os.path.exists(LOG_DIR):
        shutil.rmtree(LOG_DIR)
    
    os.mkdir(LOG_DIR)
    
    for size in range(MIN_SIZE, MAX_SIZE+1):
        print size        
        data = {}
        data[size] = {}
        data[size][stats.SYNTHESIS_TIME] = []
        for i in range(START_RUN, START_RUN + NUM_RUNS):
            stats_map = synth.synth(os.path.abspath('experiments/scalability/conf_{}'.format(size)))
            data[size][stats.SYNTHESIS_TIME].append(stats_map[stats.SYNTHESIS_TIME])
            data[size][stats.NUMBER_OF_PEPS] = stats_map[stats.NUMBER_OF_PEPS]
            data[size][stats.NUMBER_OF_REQUIREMENTS] = stats_map[stats.NUMBER_OF_REQUIREMENTS]
            data[size][stats.NUMBER_OF_RESOURCES] = stats_map[stats.NUMBER_OF_RESOURCES]
            data[size][stats.TEMPLATE_SIZE] = stats_map[stats.TEMPLATE_SIZE]
            dst_log_file = os.path.join(LOG_DIR, '{}_run{}.log'.format(size, i))
            shutil.copyfile(stats_map[stats.LOG_FILE], dst_log_file)