/*
 * verification_metrics.cpp
 *
 * Authors: Erickson H. da S. Alves <erickson.higor@gmail.com>
 *          Felipe R. Monteiro <rms.felipe@gmail.com>
 *
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.md', which is part of this source code package.
 * */

#ifndef __DSVERIFIER_SCRIPTS_JSCP2017_UTILS_H
#define __DSVERIFIER_SCRIPTS_JSCP2017_UTILS_H

#include <algorithm>
#include <array>
#include <memory>
#include <string>
#include <vector>
#include <cstdio>
#include <fstream>
#include <iterator>
#include <dirent.h>
#include <unistd.h>

#define BUFFER_SIZE 128
#define CURRENT_FOLDER_SYMLINK "."
#define PARENT_FOLDER_SYMLINK ".."
#define PIPE_READ_MODE "r"

namespace utils
{
    std::vector<std::string> execute_command(const char *command);
    std::vector<std::string> get_dirs();
}

#endif
