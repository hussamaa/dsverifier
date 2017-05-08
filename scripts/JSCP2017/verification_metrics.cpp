/*
 * verification_metrics.cpp
 *
 * Authors: Erickson H. da S. Alves <erickson.higor@gmail.com>
 *          Felipe R. Monteiro <rms.felipe@gmail.com>
 *
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.md', which is part of this source code package.
 * */

#include <iostream>
#include <string>
#include "dsverifier_metrics_collector_t.h"
#include "metrics_collector_t.h"
#include "utils.h"

#define DSVERIFIER "DSVERIFIER"

void calculate_metrics(metrics_collector_t &metrics_collector)
{
    double total_cpu_time = 0.0, total_wall_time = 0.0;
    std::vector<std::string> suites;
    std::vector<std::string> sub_suites;
    std::vector<std::string> test_cases;
    suites = utils::get_dirs();
    for(auto suite = suites.begin(); suite != suites.end(); ++suite)
    {
        chdir((*suite).c_str());
        std::cout << "========== SUITE: " << *suite
                << " ========== " << std::endl << std::endl;
        sub_suites = utils::get_dirs();
        for(auto sub_suite = sub_suites.begin();
                sub_suite != sub_suites.end(); ++sub_suite)
        {
            chdir((*sub_suite).c_str());
            std::cout << "====== SUBSUITE: " << *sub_suite
                    << " ====== " << std::endl << std::endl;
            test_cases = utils::get_dirs();
            double sub_suite_cpu_time = 0.0, sub_suite_wall_time = 0.0;
            double sub_suite_cpu_time_reference = 0.0;
            double sub_suite_wall_time_reference = 0.0;
            for(auto test_case = test_cases.begin();
                    test_case != test_cases.end(); ++test_case)
            {
                chdir((*test_case).c_str());
                metrics_collector.prepare_verification_task();
                double cpu_time = metrics_collector.cpu_time();
                double wall_time = metrics_collector.wall_time();
                double cpu_time_reference = metrics_collector.cpu_time_reference();
                double wall_time_reference = metrics_collector.wall_time_reference();
                auto actual_result = metrics_collector.run_verification_task();
                sub_suite_cpu_time += metrics_collector.cpu_time() - cpu_time;
                sub_suite_wall_time += metrics_collector.wall_time() - wall_time;
                sub_suite_cpu_time_reference += metrics_collector.cpu_time_reference() - cpu_time_reference;
                sub_suite_wall_time_reference += metrics_collector.wall_time_reference() - wall_time_reference;
                std::cout << " ---- " << *test_case << " " << actual_result << std::endl;
                chdir("../.");
            }
            std::cout << "TIME: [ Boost { Wall time = " <<
                sub_suite_wall_time << "s, CPU time = " <<
                sub_suite_cpu_time << "s } ] [ Time { Wall time = " <<
                sub_suite_wall_time_reference << "s, CPU time = " <<
                sub_suite_cpu_time_reference << "s } ]" << std::endl;
            std::cout << "=====================================" << std::endl;
            test_cases.clear();
            std::cout << std::endl;
            chdir("../.");
        }
        sub_suites.clear();
        std::cout << std::endl << std::endl;
        chdir("../.");
    }
    suites.clear();
    std::cout << "==========================================" << std::endl;
    std::cout << "CORRECT: " << metrics_collector.correct() << std::endl;
    std::cout << "INCORRECT: " << metrics_collector.incorrect() << std::endl;
    std::cout << "FALSE CORRECT: " << metrics_collector.false_correct() << std::endl;
    std::cout << "FALSE INCORRECT: " << metrics_collector.false_incorrect() << std::endl;
    std::cout << "NOT SUPPORTED: " << metrics_collector.not_supported() << std::endl;
    std::cout << "TOTAL TIME: [ Boost { Wall time = " <<
            metrics_collector.wall_time() << "s, CPU time = " <<
            metrics_collector.cpu_time() << "s } ] [ Time { Wall time = " <<
            metrics_collector.wall_time_reference() << "s, CPU time = " <<
            metrics_collector.cpu_time_reference() << "s } ]" << std::endl;
    std::cout << "==========================================" << std::endl;
}

int main(int argc, const char **argv)
{
    if(argc == 1)
    {
        metrics_collector_t *metrics_collector = new dsverifier_metrics_collector_t;
        calculate_metrics(*metrics_collector);
        delete metrics_collector;
    }
    else
    {
        std::cout << "ERROR::Too many arguments provided." << std::endl;
    }
    return 0;
}
