import array
import random
import json

import numpy

from deap import algorithms
from deap import base
from deap import creator
from deap import tools

with open("../src/main/scala/org/tygus/suslik/synthesis/tactics/orderOfRules.json", "r") as json_file:
    json_data = json.load(json_file)

numbOfAnyPhaseRules = json_data["numbOfAnyPhaseRules"]
orderOfAnyPhaseRules = json_data["orderOfAnyPhaseRules"]

def main():
    print(numbOfAnyPhaseRules)
    print(orderOfAnyPhaseRules)
    return 0

if __name__ == "__main__":
    main()
