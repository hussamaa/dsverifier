#include <dsverifier.h>

digital_system controller = {
        .a = { 1.0, 1.3, 0.17, -0.157, 0.0126},
        .a_size = 5,
        .b = {0.15, -0.075, -0.051, 0.012},
        .b_size = 4,
        .sample_time = 0.01
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 16,
        .delta = 0.25,
        .max = 1.0,
        .min = -1.0,
        .scale = 1
};

digital_system plant = {
        .b = { 2.0, -4.0 },
        .b_size = 2,
        .a = { 1.0, -0.1, -0.3 },
        .a_size = 3
};
