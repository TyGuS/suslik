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
    print("Hello from evolutionary_post_process.py")
    print(roboevaluation.SUSLIK_JAR)
    print(evolutionary.default_groups[0].start_at_tuned_order)

    for experiment in evolutionary.experiments:
        print("experiment_id is")
        print(experiment.experiment_id)
        for group in evolutionary.default_groups:

            print("group_id is")
            print(group.group_id)

            group.set_experiment_id(experiment.experiment_id)
            with open(group.json_final_overall_result_file_path(is_for_training=True),
                      'r') as final_overall_training_result:
                json_overall_training_result = final_overall_training_result.read()

            overall_training_result = json.loads(json_overall_training_result)
            numb_of_generations = len(overall_training_result["overall_result"])
            index_of_the_last_generation = numb_of_generations - 1
            training_result_list = overall_training_result["overall_result"]
            last_generation_training_result = training_result_list[index_of_the_last_generation]
            print("ancestor ranks on a training dataset are:")
            print(last_generation_training_result["ancestor_ranks"])

            numbers_of_nans_training = []
            for top_individual_in_a_generation in training_result_list:
                numbers_of_nans_training.append(top_individual_in_a_generation["number_of_nan"])
            print("number of unsolved prolems by ancestors are:")
            print(numbers_of_nans_training)

            with open(group.json_final_overall_result_file_path(is_for_training=False),
                      'r') as final_overall_validation_result:
                json_overall_validation_result = final_overall_validation_result.read()

            # The validation set and training set should have the same number of generations.
            overall_validation_result = json.loads(json_overall_validation_result)
            validation_result_list = overall_validation_result['overall_result']
            last_generation_validation_result = validation_result_list[index_of_the_last_generation]
            print("number of unsolved problems in the training dataset by ancestors are:")
            print(last_generation_validation_result['ancestor_ranks'])
            numbers_of_nans_validation = []
            for top_individual_in_a_generation in validation_result_list:
                numbers_of_nans_validation.append(top_individual_in_a_generation['number_of_nan'])
            print("number of unsolved problems in the validation dataset by ancestors are:")
            print(numbers_of_nans_validation)

            print("hohoho <-",(* numbers_of_nans_validation,))
            baseline = []
            for _ in validation_result_list:
                baseline.append(1.0)
            print("baseline <- c", (* baseline,))
            print("hohoho <-", (*numbers_of_nans_validation,))
            print('plot(baseline,type = "l",col = "black", xlab = "generation", ' +
                  'ylab = "unsolved goals within 3 seconds")')

            print('lines(runtime_weight, type="b", col="black", pch="25"')



if __name__ == "__main__":
    main()