#include <dsverifier.h>

digital_system controller = {
        .b = { 0.91796875f, 0.0f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.375f, 0.0f, 0.0f },
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
        .b = { 8.0117E-4, 1.9183E-4 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 1.0f, -1.0062f, 0.0067f },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
};

