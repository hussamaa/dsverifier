#include <dsverifier.h>

digital_system controller = {
        .b = { 0.3896484375f, 0.09375f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.8125f, 0.123046875f },
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
        .b = { 0.3134f, 0.6048f, 0.2693f, -0.0221f },
        .b_uncertainty = { 0.0, 0.0, 0.0, 0.0 },
        .b_size = 4,
        .a = { 1.0f, 0.1591, 0.0064, -3.4566E-13, 1.4765E-45 },
        .a_uncertainty = { 0.0, 0.0, 0.0, 0.0, 0.0 },
        .a_size = 5,
};

