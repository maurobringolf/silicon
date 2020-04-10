#!/usr/bin/env python3

import csv
import subprocess
import matplotlib.pyplot as plt
import numpy as np
from os.path import basename
import argparse

parser = argparse.ArgumentParser(description='Create a plot illustrating the performance difference between two Silicon commits (or branches, tags, etc).')
parser.add_argument('--base', metavar='base', type=str, nargs=1, default='source/master', dest='BASE',
                   help='Base version')
parser.add_argument('--cmp', metavar='cmp', type=str, nargs=1,default='master', dest='CMP',
                   help='Compared version')
parser.add_argument('--testClass', metavar='testClass', type=str, nargs=1,default='FrontendGeneratedTests', dest='TESTCLASS',
                   help='Name of the Scala test class to be run')
parser.add_argument('-p', dest='PLOTONLY',action='store_true',
                   help='Only plot the data that is stored in the presumably already existing CSV files.')


def shouldIncludeTest(baseResults, compareResults):
    return baseResults == compareResults

def checkoutAndRun(config):
    subprocess.run(f'git checkout {config.BASE}', shell=True)
    subprocess.run(f'git checkout {config.CMP} -- src/test/scala/{config.TESTCLASS}.scala', shell=True)
    subprocess.run(f'sbt -J-Xss32m "test:runMain -DSILICONTESTS_TARGET=./target -DSILICONTESTS_WARMUP=./warmup -DSILICONTESTS_REPETITIONS=5 -DSILICONTESTS_CSV={config.TMPDIR}/{config.BASECSV} org.scalatest.tools.Runner -o -s viper.silicon.tests.{config.TESTCLASS}"', shell=True)
    subprocess.run(f'git checkout -f {config.CMP}', shell=True)
    subprocess.run(f'sbt -J-Xss32m "test:runMain -DSILICONTESTS_TARGET=./target -DSILICONTESTS_WARMUP=./warmup -DSILICONTESTS_REPETITIONS=5 -DSILICONTESTS_CSV={config.TMPDIR}/{config.CMPCSV} org.scalatest.tools.Runner -o -s viper.silicon.tests.{config.TESTCLASS}"',shell=True)

def makePlot(config):
    differences = []
    with open(f'tmp_csv/{config.BASECSV}', newline='') as base:
        with open(f'tmp_csv/{config.CMPCSV}', newline='') as compare:
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
            plt.xticks( range(len(names))
                      #, names
                      , rotation=90)

            matplotlib.pyplot.table(names)

            plt.plot(range(len(names)), meanSlowdown, "ko--", label="relative slowdown (mean) [%]")
            plt.plot(range(len(names)), bestSlowdown, "go", label="relative slowdown (best) [%]")
            plt.plot(range(len(names)), worstSlowdown, "ro", label="relative slowdown (worst) [%]")

            plt.legend()
            plt.savefig(f"{config.TMPDIR}/performance-diff.png")

if __name__ == "__main__":

    config = parser.parse_args()

    config.TESTCLASS = 'FrontendGeneratedTests'

    config.BASECSV = config.BASE.replace("/", "_") + ".csv"
    config.CMPCSV = config.CMP.replace("/", "_") + ".csv"
    config.TMPDIR = 'tmp_csv'

    if not config.PLOTONLY:
        #checkoutAndRun(config)
        pass

    x = subprocess.run(f'git status --porcelain', shell=True,capture_output=True,text=True)

    if(x.stdout.strip() != ""):
        exit("ABORTED: It seems that you have are not in a clean git state. Commit everything first.")

    makePlot(config)
