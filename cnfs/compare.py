import os

import subprocess

from colorama import init as colorama_init
from colorama import Fore
from colorama import Style

import time

colorama_init()

tests = []
dirs = os.listdir()
dirs.sort()
for dir in dirs:
    if os.path.isfile(dir):
        if dir.split('.')[1] == 'cnf':
            if dir in ["add16.cnf", "add32.cnf", "add64.cnf", "add128.cnf"]:
                continue
            tests.append(dir)

start = time.time()
for test in tests:
    os.system("/Users/timo/Kissat/kissat/build/kissat " + test)
end = time.time()
time1 = end - start

start = time.time()
for test in tests:
    os.system(".././babysat " + test)
end = time.time()
time2 = end - start

print("")
print("")
print("")
print("")
print("")
print("")
print("")
print("")
print("")

# Time 1 is Kissat
# Time 2 is Babysat
print(Fore.GREEN + "Kissat: " + Style.RESET_ALL + str(round(time1, 5)) + "s")
print(Fore.RED + "Babysat: " + Style.RESET_ALL + str(round(time2, 5)) + "s")