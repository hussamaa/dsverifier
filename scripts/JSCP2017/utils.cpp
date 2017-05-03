/*
 * verification_metrics.cpp
 *
 * Authors: Erickson H. da S. Alves <erickson.higor@gmail.com>
 *          Felipe R. Monteiro <rms.felipe@gmail.com>
 *
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.md', which is part of this source code package.
 * */

#include "utils.h"

std::vector<std::string> utils::execute_command(const char *command)
{
    std::array<char, BUFFER_SIZE> buffer;
    std::vector<std::string> result;
    std::shared_ptr<FILE> pipe(popen(command, PIPE_READ_MODE), pclose);
    if(pipe)
    {
        while(!feof(pipe.get()))
        {
            if(fgets(buffer.data(), BUFFER_SIZE, pipe.get()) != nullptr)
            {
                auto data = std::string(buffer.data());
                result.push_back(data.substr(0, data.length() - 1));
            }
        }
    }
    return result;
}

std::vector<std::string> utils::get_dirs()
{
    DIR *dir;
    struct dirent *ent;
    std::vector<std::string> dirs;
    if((dir = opendir(CURRENT_FOLDER_SYMLINK)) != nullptr)
    {
        while((ent = readdir(dir)) != nullptr)
        {
            if(ent->d_type == DT_DIR)
            {
                auto current_dir = std::string(ent->d_name);
                if(current_dir.compare(CURRENT_FOLDER_SYMLINK) != 0 &&
                    current_dir.compare(PARENT_FOLDER_SYMLINK) != 0)
                    dirs.push_back(current_dir);
            }
        }
        closedir(dir);
        std::sort(dirs.begin(), dirs.end());
    }
    return dirs;
}
