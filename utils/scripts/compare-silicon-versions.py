#!/usr/bin/env python3

import csv
import subprocess
import matplotlib.pyplot as plt
import numpy as np

from os.path import basename

def shouldIncludeTest(baseResults, compareResults):
    return baseResults == compareResults

# TODO Read from arguments
BASE='source/master'
CMP='master'
TESTCLASS='FrontendGeneratedTests'

BASECSV=BASE.replace("/", "_") + ".csv"
CMPCSV=CMP.replace("/", "_") + ".csv"

subprocess.run(f'git checkout {BASE}', shell=True)
subprocess.run(f'git checkout {CMP} -- src/test/scala/{TESTCLASS}.scala', shell=True)
subprocess.run(f'sbt -J-Xss32m "test:runMain -DSILICONTESTS_TARGET=./target -DSILICONTESTS_WARMUP=./warmup -DSILICONTESTS_REPETITIONS=5 -DSILICONTESTS_CSV=tmp_csv/{BASECSV} org.scalatest.tools.Runner -o -s viper.silicon.tests.{TESTCLASS}"', shell=True)
subprocess.run(f'git checkout -f {CMP}', shell=True)
subprocess.run(f'sbt -J-Xss32m "test:runMain -DSILICONTESTS_TARGET=./target -DSILICONTESTS_WARMUP=./warmup -DSILICONTESTS_REPETITIONS=5 -DSILICONTESTS_CSV=tmp_csv/{CMPCSV} org.scalatest.tools.Runner -o -s viper.silicon.tests.{TESTCLASS}"',shell=True)

differences = []


with open(f'tmp_csv/{BASECSV}', newline='') as base:
    with open(f'tmp_csv/{CMPCSV}', newline='') as compare:
        baseR = csv.reader(base, delimiter=',', quotechar='|')
        compareR = csv.reader(compare, delimiter=',', quotechar='|')

        # Skip header row
        next(baseR)
        next(compareR)

        # Filter out all tests with unequal verification results
        relevantTests = filter(lambda x: shouldIncludeTest(x[0][8], x[1][8]), zip(baseR, compareR))

        names = []
        meanSlowdown = []
        bestSlowdown = []
        worstSlowdown = []
        relStdDevDiff = []

        for t in relevantTests:
            base = t[0]
            cmp = t[1]
            names += [base[0]]
            meanSlowdown += [round(100 * (int(cmp[2]) - int(base[2])) / int(cmp[2]), 1)]
            bestSlowdown += [round(100 * (int(cmp[5]) - int(base[5])) / int(cmp[5]), 1)]
            worstSlowdown += [round(100 * (int(cmp[7]) - int(base[7])) / int(cmp[7]), 1)]
            relStdDevDiff += [int(cmp[4]) - int(base[4])]


        axes = plt.gca()
        plt.xticks(range(len(names)), rotation=90)

        plt.plot(range(len(names)), meanSlowdown, "ko--", label="relative slowdown (mean) [%]")
        plt.plot(range(len(names)), bestSlowdown, "go", label="relative slowdown (best) [%]")
        plt.plot(range(len(names)), worstSlowdown, "ro", label="relative slowdown (worst) [%]")


        plt.legend()
        plt.savefig('tmp_csv/performance-diff.png')

