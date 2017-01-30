#include <dsverifier.h>

digital_system controller = {
        .b = { 1.5f, -1.2f },
        .b_size = 2,
        .a = { 1.0f, 0.5f },
        .a_size = 2,
        .sample_time = 1
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0,
        .scale = 1
};

digital_system plant = {
        .b = { 0.5f, 0.5f },
        .b_size = 2,
        .a = { 2.0f, -2.0f, 1.0f },
        .a_size = 3
};

