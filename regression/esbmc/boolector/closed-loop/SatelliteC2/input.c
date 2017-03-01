#include <dsverifier.h>

digital_system controller = {
        .b = { 0.43f, -0.2408f, -0.1316f },
        .b_size = 3,
        .a = { 1.0f, 1.5f, 0.97f, 0.183f },
        .a_size = 4,
        .sample_time = 2
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 5,
        .max = 1.0,
        .min = -1.0,
        .scale = 1
};

digital_system plant = {
        .b = { 2.0f, 2.0f },
        .b_size = 2,
        .a = { 1.0f, -2.0f, 1.0f },
        .a_size = 3
};

