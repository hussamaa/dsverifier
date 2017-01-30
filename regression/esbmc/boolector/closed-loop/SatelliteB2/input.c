#include <dsverifier.h>

digital_system controller = {
        .b = { 2.88f, -4.896f, 2.074f },
        .b_size = 3,
        .a = { 1.0f, -0.42f, -0.3465f, -0.03915f },
        .a_size = 4,
        .sample_time = 1
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0,
        .scale = 1
};

digital_system plant = {
        .b = { 0.125f, 0.125f },
        .b_size = 2,
        .a = { 1.0f, -2.0f, 1.0f },
        .a_size = 3
};

