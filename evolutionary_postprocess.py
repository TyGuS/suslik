import os
import json
import pandas
import csv
import evolutionary
import roboevaluation
# -----------------------
# This file produces
# Call this Python script only after running evolutionary.py.
# -----------------------
def main():

    training_or_validation = ['training', 'validation']

    for experiment in evolutionary.experiments:

        for type_of_run in training_or_validation:
            print()
            print('### Experiment ID:', str(experiment.experiment_id) + ", Type:", type_of_run, '###')

            if type_of_run == 'training':
                is_for_training = True
                number_of_data_str = 'number_of_training_data'
            else:
                is_for_training = False
                number_of_data_str = 'number_of_validation_data'

            baseline = []
            generation_index = 0
            while generation_index <= evolutionary.MAXIMUM_NUMBER_OF_GENERATIONS:
                baseline.append(1.0)
                generation_index += 1

            print("baseline <- c", (*baseline,))
            print('plot(baseline,type="l", col="black", xlab="generation", ' +
                  'ylab="unsolved goals within ' + str(experiment.short_timeout) + ' milliseconds")')

            pch = 0
            for group in evolutionary.default_groups:

                # Group is shared by multiple experiments. So, we have to set experiment_id here.
                group.set_experiment_id(experiment.experiment_id)

                with open(group.json_final_overall_result_file_path(is_for_training=is_for_training), 'r') \
                        as final_overall_result:
                    json_overall_result = final_overall_result.read()

                overall_result = json.loads(json_overall_result)
                numb_of_generations = len(overall_result["overall_result"])
                index_of_the_last_generation = numb_of_generations - 1
                result_list = overall_result["overall_result"]

                number_of_data = result_list[0][number_of_data_str]
                number_of_data_str = str(number_of_data)

                numbers_of_unsolved_goals = []
                for top_individual_in_a_generation in result_list:
                    numbers_of_unsolved_goals.append(top_individual_in_a_generation['number_of_nan'])

                relative_numbers_of_unsolved_goals = []
                for number_of_unsolved_goals in numbers_of_unsolved_goals:
                    relative_numbers_of_unsolved_goals.append(number_of_unsolved_goals / numbers_of_unsolved_goals[0])

                print("relative_number_of_unsolved_goals_in_group_" + str(group.group_id), "<- c",
                      (*relative_numbers_of_unsolved_goals,))
                print('lines(' + "relative_number_of_unsolved_goals_in_group_" + str(group.group_id) +
                      ', type="b", col="black", pch="' + str(pch) + '")')


if __name__ == "__main__":
    main()