/*
 * verification_metrics.cpp
 *
 * Authors: Erickson H. da S. Alves <erickson.higor@gmail.com>
 *          Felipe R. Monteiro <rms.felipe@gmail.com>
 *
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.md', which is part of this source code package.
 * */

#include "metrics_collector_t.h"

metrics_collector_t::~metrics_collector_t()
{
}

std::string metrics_collector_t::get_expected_result() const
{
    std::ifstream test_description;
    std::string line, result;
    test_description.open(TEST_DESCRIPTION_FILE);
    while(!(test_description.eof()))
    {
       std::getline(test_description, line);
       if(line.at(0) == TEST_DESCRIPTION_DELIMITER)
       {
          result = line.substr(1, line.size() - 2);
          break;
       }
    }
    test_description.close();
    return result;
}

void metrics_collector_t::parse_time_output(const std::vector<std::string>& output,
                                            double& system_cpu_time,
                                            double& user_cpu_time,
                                            double& wall_time) const
{
    std::string system_cpu_time_str, user_cpu_time_str, wall_time_str;
    for(const auto& message : output)
    {
        if(std::regex_match(message, std::regex(SYSTEM_CPU_TIME_REGEX)))
        {
            const std::size_t last_whitespace = message.find_last_of(WHITESPACE);
            system_cpu_time_str = message.substr(last_whitespace + 1);
            system_cpu_time = std::stod(system_cpu_time_str);
        }
        if(std::regex_match(message, std::regex(USER_CPU_TIME_REGEX)))
        {
            const std::size_t last_whitespace = message.find_last_of(WHITESPACE);
            user_cpu_time_str = message.substr(last_whitespace + 1);
            user_cpu_time = std::stod(user_cpu_time_str);
        }
        if(std::regex_match(message, std::regex(WALL_TIME_REGEX)))
        {
            const std::size_t last_whitespace = message.find_last_of(WHITESPACE);
            wall_time_str = message.substr(last_whitespace + 1);
            const std::size_t semicolon = wall_time_str.find(SEMICOLON);
            std::string m, s;
            m = wall_time_str.substr(0, semicolon);
            s = wall_time_str.substr(semicolon + 1);
            wall_time = std::stod(m) * MINUTES_TO_SECONDS_FACTOR + std::stod(s);
        }
    }
}


void metrics_collector_t::prepare_verification_task()
{
}

std::string metrics_collector_t::run_verification_task()
{
    return "";
}
