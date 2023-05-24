import os

from colorama import init as colorama_init
from colorama import Fore
from colorama import Style

import time

colorama_init()

time1 = []
time2 = []

tests = []
dirs = os.listdir()
dirs.sort()
for dir in dirs:
    if os.path.isfile(dir):
        if dir.split('.')[1] == 'cnf':
            if dir in ["add16.cnf", "add32.cnf", "add64.cnf", "add128.cnf",
                       "prime65537.cnf"
                       ]:
                continue
            tests.append(dir)

for i in range(10):
    start = time.time()
    for test in tests:
        os.system("/Users/timo/Kissat/kissat/build/kissat " + test + " -q")
        #print("/Users/timo/Kissat/kissat/build/kissat " + test + " -q")
    end = time.time()
    time1.append(end - start)

    start = time.time()
    for test in tests:
        os.system(".././babysat " + test + " -q")
        #print(".././babysat " + test + " -q")
    end = time.time()
    time2.append(end - start)

print("\n \n \n \n")
print("\n \n \n \n")
print("\n \n \n \n")
print("\n \n \n \n")
print("\n \n \n \n")
print("\n \n \n \n")
print("\n \n \n \n")

# Time 1 is Kissat
# Time 2 is Babysat
time1_sum = 0
time2_sum = 0
time1_max = 0
time2_max = 0
for i in range(len(time1)):
    time1_sum += time1[i]
    time2_sum += time2[i]
    if time1[i] > time1_max:
        time1_max = time1[i]
    if time2[i] > time2_max:
        time2_max = time2[i]
time1_avg = time1_sum / len(time1)
time2_avg = time2_sum / len(time2)

print(Fore.GREEN + "Kissat: \n" + Style.RESET_ALL +
      "    Average Time: " + str(round(time1_avg, 5)) + "s \n" +
      "    Max Time: " + str(round(time1_max, 5)) + "s \n")
print()
print(Fore.RED + "Babysat: \n" + Style.RESET_ALL +
      "    Average Time: " + str(round(time2_avg, 5)) + "s \n" +
      "    Max Time: " + str(round(time2_max, 5)) + "s \n")