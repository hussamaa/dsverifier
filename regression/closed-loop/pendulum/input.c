#include <dsverifier.h>

digital_system controller = {
        .b = { -0.96484375, 0.9833984375 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.8896484375, -0.875, 0 },
        .a_uncertainty = { 0.0, 0.0, 0.0  },
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
        .b = { 0.2039f, 0.2039f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 1.0f, 1.19999f, 1.0f },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
};

