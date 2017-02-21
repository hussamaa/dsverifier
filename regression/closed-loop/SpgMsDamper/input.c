#include <dsverifier.h>

digital_system controller = {
        .b = { -0.0000000004656612873077392578125, 1.0000000004656612873077392578125, -1.0000000004656612873077392578125},
        .b_uncertainty = { 0.0, 0.0, 0.0 },
        .b_size = 3,
        .a = { 1, -0.0000000004656612873077392578125, 0.0000000004656612873077392578125},
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
        .b = { 5.000000e-5, 5.000000e-5 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 1.000000, -2.000000, 1.000000 },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
};

