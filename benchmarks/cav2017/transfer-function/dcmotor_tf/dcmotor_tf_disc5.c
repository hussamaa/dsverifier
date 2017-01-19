#include <dsverifier.h>

digital_system controller = {
        .b = { 0.8125f, 0.0f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.53125f, 0.0f, 0.0f },
        .a_uncertainty = { 0.0f, 0.0f, 0.0f },
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
        .b = { 0.0197f, 1.9795E-4 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 1.0f, -0.9897f, -1.0987E-16 },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
};

