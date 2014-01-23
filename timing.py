from subprocess import Popen, PIPE
import sys
import time

if len(sys.argv) < 2:
    print "Usage: python time.py file.v"
    exit()

p = Popen(['coqtop'], shell=True, stdin=PIPE, stdout=PIPE, stderr=PIPE)

def read_result():
    read = ""
    while read != "<":
        read = p.stderr.read(1)

read_result() # Initial prompt

for line in open(sys.argv[1]):
    print line.strip()
    start = time.time()
    p.stdin.write(line)
    read_result()
    print time.time() - start

p.terminate()
