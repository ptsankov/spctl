OUTPUT_FILE = None

DEBUG = True

def setOutputFile(outFile):
    global OUTPUT_FILE
    OUTPUT_FILE = outFile

def write(s):
    assert OUTPUT_FILE is not None
    if DEBUG:
        print s
    OUTPUT_FILE.write(s)
    
def close():
    OUTPUT_FILE.close()