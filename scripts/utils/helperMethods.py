OUTPUT_FILE = None

def setOutputFile(outFile):
    global OUTPUT_FILE
    OUTPUT_FILE = outFile

def write(s):
    assert OUTPUT_FILE is not None
    OUTPUT_FILE.write(s)
