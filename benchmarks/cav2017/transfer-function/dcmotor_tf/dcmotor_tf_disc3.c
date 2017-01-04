#include <dsverifier.h>

digital_system controller = {
        .b = { 0.703125f, 0.208984375f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.0f, 0.001953125f },
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
        .b = { 0.0973f, 1.8989E-4 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 1.0f, -0.9493f },
        .a_uncertainty = { 0.0, 0.0 },
        .a_size = 2,
};

