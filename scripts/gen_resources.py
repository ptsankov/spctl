import sys

f = open(sys.argv[1])
numFloors = int(sys.argv[2])

lines = [x.strip() for x in f.readlines()]
for i in range(numFloors):
    for l in lines:
        for r in l.split(' '):
            if r == 'out':
                continue
            if r != 'elev':
                print(r + '_' + str(i)),
            else:
                print r,
        print ''

print 'elev ',
for i in range(numFloors):
    print 'cor1_' + str(i), 