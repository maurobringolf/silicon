#!/usr/bin/env python3

import csv

differences = []

def shouldIncludeTest(baseResults, compareResults):
    return baseResults == compareResults

def cmpTest(base, cmp):
    return { 'name': base[0]
           , 'relative slowdown (mean) [%]':  round(100 * (int(cmp[2]) - int(base[2])) / int(cmp[2]), 1)
           , 'relative slowdown (best) [%]':  round(100 * (int(cmp[5]) - int(base[5])) / int(cmp[5]), 1)
           , 'relative slowdown (worst) [%]':  round(100 * (int(cmp[7]) - int(base[7])) / int(cmp[7]), 1)
           , 'RelStdDev difference [%]': int(cmp[4]) - int(base[4])
           }

with open('logs/20-03-09-source-master.csv', newline='') as base:
    with open('logs/20-03-09-fork-master.csv', newline='') as compare:
        baseR = csv.reader(base, delimiter=',', quotechar='|')
        compareR = csv.reader(compare, delimiter=',', quotechar='|')

        # Skip header row
        next(baseR)
        next(compareR)

        # Filter out all tests with unequal verification results
        relevantTests = filter(lambda x: shouldIncludeTest(x[0][8], x[1][8]), zip(baseR, compareR))

        differences = map(lambda x: cmpTest(x[0], x[1]), relevantTests)

        for d in differences:
            print(d)
