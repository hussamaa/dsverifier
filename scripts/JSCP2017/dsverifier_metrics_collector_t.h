/*
 * verification_metrics.cpp
 *
 * Authors: Erickson H. da S. Alves <erickson.higor@gmail.com>
 *          Felipe R. Monteiro <rms.felipe@gmail.com>
 *
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.md', which is part of this source code package.
 * */

#ifndef __DSVERIFIER_SCRIPTS_JSCP2017_DSVERIFIER_METRICS_COLLECTOR_T_H
#define __DSVERIFIER_SCRIPTS_JSCP2017_DSVERIFIER_METRICS_COLLECTOR_T_H

#include <boost/chrono.hpp>
#include <regex>
#include <string>
#include <vector>
#include "metrics_collector_t.h"

#ifdef __APPLE__ || __MACH__
#define DSVERIFIER_RUN_COMMAND_BASE "gtime -v gtimeout 600s dsverifier 2>&1 input.c "
#else
#define DSVERIFIER_RUN_COMMAND_BASE "/usr/bin/time -v timeout 600s dsverifier 2>&1 input.c "
#endif

#define TEST_DESC_PARAMETER_REGEX ".*--property.*"
#define PARSING_ERROR_REGEX ".*PARSING ERROR.*"
#define UNWINDING_ASSERTION_LOOP_REGEX ".*unwinding assertion loop.*"
#define CONVERSION_ERROR_REGEX ".*CONVERSION ERROR.*"

class dsverifier_metrics_collector_t: public metrics_collector_t
{
public:
    dsverifier_metrics_collector_t()
    {
    }

    ~dsverifier_metrics_collector_t()
    {
    }

    void prepare_verification_task()
    {
        std::ifstream test_description;
        std::string line, command;
        test_description.open(TEST_DESCRIPTION_FILE);
        while(!(test_description.eof()))
        {
            std::getline(test_description, line);
            if(std::regex_match(line, std::regex(TEST_DESC_PARAMETER_REGEX)))
            {
                command = line;
                break;
            }
        }
        test_description.close();
        m_command = DSVERIFIER_RUN_COMMAND_BASE + command;
    }

    std::string run_verification_task()
    {
        bool successful = true, supported = true;
        double system_cpu_time, user_cpu_time;
        double system_cpu_time_reference, user_cpu_time_reference;
        double current_cpu_time, current_wall_time;
        double current_cpu_time_reference, current_wall_time_reference;
        boost::chrono::process_real_cpu_clock::time_point w_start = boost::chrono::process_real_cpu_clock::now();
        boost::chrono::process_system_cpu_clock::time_point sc_start = boost::chrono::process_system_cpu_clock::now();
        boost::chrono::process_user_cpu_clock::time_point uc_start = boost::chrono::process_user_cpu_clock::now();
        std::vector<std::string> run_command_output = utils::execute_command(m_command.c_str());
        boost::chrono::process_real_cpu_clock::time_point w_end = boost::chrono::process_real_cpu_clock::now();
        boost::chrono::process_system_cpu_clock::time_point sc_end = boost::chrono::process_system_cpu_clock::now();
        boost::chrono::process_user_cpu_clock::time_point uc_end = boost::chrono::process_user_cpu_clock::now();
        current_wall_time = boost::chrono::duration_cast<boost::chrono::nanoseconds>(w_end - w_start).count() / BILLION;
        system_cpu_time = boost::chrono::duration_cast<boost::chrono::nanoseconds>(sc_end - sc_start).count() / BILLION;
        user_cpu_time = boost::chrono::duration_cast<boost::chrono::nanoseconds>(uc_end - uc_start).count() / BILLION;
        current_cpu_time = system_cpu_time + user_cpu_time;
        parse_time_output(run_command_output,
                system_cpu_time_reference, user_cpu_time_reference, current_wall_time_reference);
        current_cpu_time_reference = system_cpu_time_reference + user_cpu_time_reference;
        m_cpu_time += current_cpu_time;
        m_wall_time += current_wall_time;
        m_cpu_time_reference += current_cpu_time_reference;
        m_wall_time_reference += current_wall_time_reference;
        for(const auto &message : run_command_output)
        {
            if(message.find(VERIFICATION_FAILED_MESSAGE) != std::string::npos)
            {
                successful = false;
                break;
            }
            else if(std::regex_match(message, std::regex(CONVERSION_ERROR_REGEX)) ||
                    std::regex_match(message, std::regex(PARSING_ERROR_REGEX)) ||
                    std::regex_match(message, std::regex(UNWINDING_ASSERTION_LOOP_REGEX)))
            {
                supported = false;
                break;
            }
        }
        std::string expected_result = get_expected_result();
        std::string actual_result;
        if(!supported)
        {
            ++m_not_supported;
            actual_result = NOT_SUPPORTED_RESULT;
        }
        else
        {
            if(successful && expected_result.compare(VERIFICATION_SUCCESSFUL_MESSAGE) == 0)
            {
                ++m_correct;
                actual_result = CORRECT_RESULT;
            }
            else if(successful && expected_result.compare(VERIFICATION_FAILED_MESSAGE) == 0)
            {
                ++m_false_correct;
                actual_result = FALSE_CORRECT_RESULT;
            }
            else if(!successful && expected_result.compare(VERIFICATION_FAILED_MESSAGE) == 0)
            {
                ++m_incorrect;
                actual_result = INCORRECT_RESULT;
            }
            else if(!successful &&
                    expected_result.compare(VERIFICATION_SUCCESSFUL_MESSAGE) == 0)
            {
                ++m_false_incorrect;
                actual_result = FALSE_INCORRECT_RESULT;
            }
        }
        actual_result += " [ Boost = { Wall time: " +
                std::to_string(current_wall_time) + "s, CPU time: " +
                std::to_string(current_cpu_time) +  "s } ]";
        actual_result += " [ Time = { Wall time: " +
                std::to_string(current_wall_time_reference) + "s, CPU time: " +
                std::to_string(current_cpu_time_reference) +  "s } ]";
        return actual_result;
    }
private:
    std::string m_command;
};

#endif
