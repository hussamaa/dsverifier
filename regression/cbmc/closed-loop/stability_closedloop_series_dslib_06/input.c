#include "../../../bmc/dsverifier.h"

digital_system controller = {
        .a = {1.0, -0.5, -0.55, 0.185, -0.0126},
        .a_size = 5,
        .b = {0.1, 0.03, -0.01},
        .b_size = 3,
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
