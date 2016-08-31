#include <dsverifier.h>

digital_system controller = {
        .b = { 0.2f, -0.18f },
        .b_size = 2,
        .a = { 1.0f, 0.3f },
        .a_size = 2,
        .sample_time = 2
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 16,
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

