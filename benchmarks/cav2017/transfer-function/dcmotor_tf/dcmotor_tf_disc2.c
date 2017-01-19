#include <dsverifier.h>

digital_system controller = {
        .b = { 0.3544921875f, 0.0f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.1826171875f, 0.0625f, 0.0f },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
        .sample_time = 2,
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0,
        .scale = 1,
};

digital_system plant = {
        .b = { 7.3573e-5, 5.2845e-5 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 1.0f, -1.3678f, 0.3678 },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
};

