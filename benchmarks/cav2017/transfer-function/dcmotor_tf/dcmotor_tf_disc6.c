#include <dsverifier.h>

digital_system controller = {
        .b = { 0.75f },
        .b_uncertainty = { 0.0 },
        .b_size = 1,
        .a = { 0.8994140625f, 0.4833984375f },
        .a_uncertainty = { 0.0, 0.0 },
        .a_size = 2,
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
        .b = { 0.0098f, 1.9898E-4 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 1.0f, -0.9948f, -1.1045E-16 },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
};

