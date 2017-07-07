#include <dsverifier.h>

digital_system controller = {
        .b = { 11.04f, -5.864f, 4.902f },
        .b_uncertainty = { 0.0, 0.0, 0.0 },
        .b_size = 3,
        .a = { 3.402823e+39f, 0.06311f, 0.1284f },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
        .sample_time = 0.2
};

implementation impl = {
        .int_bits = 5,
        .frac_bits = 16,
        .max = 1.0,
        .min = -1.0,
        .scale = 1,
};

digital_system plant = {
        .b = { 0.0264f },
        .b_uncertainty = { 0.0 },
        .b_size = 1,
        .a = { 1.0f, -0.9998f },
        .a_uncertainty = { 0.0, 0.0 },
        .a_size = 2,
};

