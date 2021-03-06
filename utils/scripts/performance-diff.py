#!/usr/bin/env python3

import csv
import sys
import subprocess
import matplotlib.pyplot as plt
import numpy as np
from os.path import basename
import argparse

csv.field_size_limit(sys.maxsize)

parser = argparse.ArgumentParser(description='Create a plot illustrating the performance difference between two Silicon commits (or branches, tags, etc).')
parser.add_argument('--base', metavar='base', type=str, default='source/master', dest='BASE', help='Base version')
parser.add_argument('--cmp', metavar='cmp', type=str, default='master', dest='CMP', help='Compared version')
parser.add_argument('--testClass', metavar='testClass', type=str, default='FrontendGeneratedTests', dest='TESTCLASS', help='Name of the Scala test class to be run')
parser.add_argument('--run', dest='RUN',action='store_true', help='Actually do the test run. Default behavior only creates the plot from presumably existing CSV files.')

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

            baseResults = list(baseR)
            compareResults = list(compareR)

            # Join on equal verification outputs
            relevantTests = []

            for b in list(baseResults):
                for c in list(compareResults):
                    if b[0] == c[0] and b[8] == c[8] and float(b[2]) > 0 and float(c[2]) > 0:
                        relevantTests.append([b, c])

            testIndex = open(f"{config.TMPDIR}/testcase-index.txt", 'w+')

            names = []
            absoluteBaseMean = []
            meanRatios = []

            y1 = []
            y2 = []
            z1 = []
            z2 = []

            for t in relevantTests:
                base = t[0]
                cmp = t[1]
                names += [base[0]]

                testIndex.write(base[0] + "\n")

                absoluteBaseMean += [int(base[2]) / 1000]

                meanRatio = float(cmp[2])/float(base[2])
                meanRatios += [meanRatio]

                print(base[0] + ", " + str(meanRatio) + ", " + str(int(base[2]) / 1000))

                y1 += [ meanRatio * (1 + float(cmp[4])/200) ]
                y2 += [ meanRatio * (1 - float(cmp[4])/200) ]
                z1 += [ meanRatio * (1 + float(base[4])/200) ]
                z2 += [ meanRatio * (1 - float(base[4])/200) ]


            #plt.xticks(range(len(names)), labels=list(map(lambda x: x + 1, range(len(names)))))

            ticks = np.arange(-1, len(names), 5)
            plt.xticks(ticks, labels=ticks+1)

            plt.plot(range(len(names)), z1, marker='_', color='black', linestyle='None', label="stdDev cmp")
            plt.plot(range(len(names)), z2, marker='_', color='black', linestyle='None')

            plt.plot(range(len(names)), y1, marker='_', color='red', linestyle='None', label="stdDev base (scaled to cmp mean)")
            plt.plot(range(len(names)), y2, marker='_', color='red', linestyle='None')

            plt.margins(0.3,0.3)

            plt.scatter(range(len(names)), meanRatios, c=absoluteBaseMean, cmap='jet')
            plt.colorbar(label='Mean base runtime [s]')
            plt.grid(color='0.9', linestyle='-', axis='x', linewidth=0.5)
            plt.axhline(y=1, color='0.9', linestyle='-', linewidth=0.5)

            plt.legend()
            plt.title("Performance distribution")


            plt.savefig(f"{config.TMPDIR}/performance-diff.png", dpi=500)

def createFileIfNotExists(fname):
    f = open(fname, 'a+')
    f.close()

if __name__ == "__main__":

    config = parser.parse_args()

    config.BASECSV = config.BASE.replace("/", "_") + ".csv"
    config.CMPCSV = config.CMP.replace("/", "_") + ".csv"
    config.TMPDIR = 'tmp_csv'

    createFileIfNotExists(f"{config.TMPDIR}/{config.BASECSV}")
    createFileIfNotExists(f"{config.TMPDIR}/{config.CMPCSV}")

    if config.RUN:
        status = subprocess.run(f'git status --porcelain', shell=True,capture_output=True,text=True)
        if(status.stdout.strip() != ""):
            exit("ABORTED: It seems that you have are not in a clean git state. Commit everything first.")
        checkoutAndRun(config)


    makePlot(config)
