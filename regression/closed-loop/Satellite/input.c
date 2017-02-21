#include <dsverifier.h>

digital_system controller = {
        .b = { 0.8359375, 0.265625, -0.96875 },
        .b_uncertainty = { 0.0, 0.0, 0.0 },
        .b_size = 3,
        .a = { 0.9453125, 0.90625, -0.15625, -0.123046875 },
        .a_uncertainty = { 0.0, 0.0, 0.0 , 0.0  },
        .a_size = 4,
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
        .b = { 1.250000e-1, 1.250000e-1 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 1.000000, -2.000000, 1.000000 },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
};

