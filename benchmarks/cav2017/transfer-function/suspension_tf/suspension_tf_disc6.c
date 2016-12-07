#include <dsverifier.h>

digital_system controller = {
        .b = { 0.224609375f, 0.83984375f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.9765625f, 0.18359375f },
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
        .b = { 0.2650f, 0.3934f, -0.0080f, -0.1365f },
        .b_uncertainty = { 0.0, 0.0, 0.0, 0.0 },
        .b_size = 4,
        .a = { 1.0f, -0.7700f, 0.2846f, -7.6677E-4, 6.1988E-12 },
        .a_uncertainty = { 0.0, 0.0, 0.0, 0.0, 0.0 },
        .a_size = 5,
};

