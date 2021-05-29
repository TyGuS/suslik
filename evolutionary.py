import array
import random
import json
from subprocess import call

import roboevaluation

import numpy

from deap import algorithms
from deap import base
from deap import creator
from deap import tools

with open("src/main/scala/org/tygus/suslik/synthesis/tactics/orderOfRules.json", "r") as jsonFile:
    jsonData = json.load(jsonFile)

numbOfAnyPhaseRules = jsonData["numbOfAnyPhaseRules"]
orderOfAnyPhaseRules = jsonData["orderOfAnyPhaseRules"]

reversedOrderOfAnyPhaseRules = orderOfAnyPhaseRules.copy()
reversedOrderOfAnyPhaseRules.reverse()

newJsonDataToWrite = {
  "numbOfAnyPhaseRules" : numbOfAnyPhaseRules,
  "orderOfAnyPhaseRules": reversedOrderOfAnyPhaseRules
}

with open("src/main/scala/org/tygus/suslik/synthesis/tactics/orderOfRulesNew.json", 'w') as newJsonFileToWrite:
  json.dump(newJsonDataToWrite, newJsonFileToWrite)

with open("src/main/scala/org/tygus/suslik/synthesis/tactics/orderOfRulesNew.json", "r") as newJsonFileToRead:
  newJsonDataToRead = json.load(newJsonFileToRead)

newNumbOfAnyPhaseRules  = newJsonDataToRead["numbOfAnyPhaseRules"]
newOrderOfAnyPhaseRules = newJsonDataToRead["orderOfAnyPhaseRules"]

def main():
    print("read a rule-odering from a json file")
    print(numbOfAnyPhaseRules)
    print(orderOfAnyPhaseRules)
    print("reverse")
    print(reversedOrderOfAnyPhaseRules)
    print("write the reversed order to a json file then read it")
    print(newNumbOfAnyPhaseRules)
    print(newOrderOfAnyPhaseRules)

    # Use robo-evaluation.py to run produce the CSV file.
    # But the CSV file should have the iteration ID and individual ID.
    pathToCSV = roboevaluation.EVAL_FOLDER + '/stats-performance-generatuin-' + str(10) + '-individual-' + str(7) + '.csv'
    results1 = roboevaluation.evaluate_n_times(1, roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS, roboevaluation.RESULTS1, roboevaluation.CSV_IN, roboevaluation.CSV_TEMP)
    roboevaluation.write_stats1(roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS, results1, pathToCSV)
    # Read the CSV file.
    import pandas as pd
    df = pd.read_csv(pathToCSV)
    print(df)
    # Compute the fitness value from the CSV file.
    totalTime = df['Time(mut)'].sum()
    print(totalTime)

    call(['java', '-jar', 'target/scala-2.12/suslik.jar', 'src/test/resources/synthesis/paper-benchmarks/ints/swap.syn', '-t=120000', '--evolutionary', 'true'])
    call(['java', '-jar', 'target/scala-2.12/suslik.jar', 'src/test/resources/synthesis/paper-benchmarks/ints/swap.syn', '-t=120000'])
    return 0

if __name__ == "__main__":
    main()
