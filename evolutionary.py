import array
import random
import json
from subprocess import call

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
    call(['java', '-jar', 'target/scala-2.12/suslik.jar', 'src/test/resources/synthesis/paper-benchmarks/ints/swap.syn', '-t=120000', '--evolutionary', 'true'])
    call(['java', '-jar', 'target/scala-2.12/suslik.jar', 'src/test/resources/synthesis/paper-benchmarks/ints/swap.syn', '-t=120000'])
    return 0

if __name__ == "__main__":
    main()
