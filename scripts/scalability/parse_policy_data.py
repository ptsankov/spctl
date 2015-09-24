#/usr/bin/python

import sys

map_size_times = {}
with open(sys.argv[1]) as f:
    content = f.readlines()
    content = [line.strip() for line in content]
    for line in content:
        if line.startswith('ors'):
            number_of_conjuncts = int(line.split(',')[0].split(' ')[1])
            number_of_enumerated_attributes = int(line.split(',')[1].split(' ')[2])
            number_of_numeric_attributes = int(line.split(',')[2].split(' ')[2])
        elif 'solving' in line:
            time = float(line.split(':')[1].strip())
            size = number_of_conjuncts * (number_of_enumerated_attributes + number_of_numeric_attributes)
            if size not in map_size_times.keys():
                map_size_times[size] = []
            map_size_times[size].append(time)
         
print 'size,time'
for size in map_size_times:
    print size,
    times = map_size_times[size]
    print reduce(lambda x, y: x + y, times) / len(times)