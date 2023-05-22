import os
import subprocess

tests = []
dirs = os.listdir()
dirs.sort()
for dir in dirs:
    if os.path.isfile(dir):
        if dir.split('.')[1] == 'cnf':
            if dir in ["add16.cnf", "add32.cnf", "add64.cnf", "add128.cnf"]:
                continue
            tests.append(dir)

for test in tests:
    #os.system(f"python3 checksolver.py --cnf-file {test} --log-file {test.split('.')[0]}.log")
    cmd = f"python3 checksolver.py --cnf-file {test} --log-file {test.split('.')[0]}.log"
    output = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE).communicate()[0].decode('utf-8')
    if (output == "Found no faults in SAT solver"):
        continue
    else:
        f"Error in {test}"
        break