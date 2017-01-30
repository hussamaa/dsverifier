#include <dsverifier.h>

digital_system controller = {
        .b = {  0.0009765625f, 0.375f },
        .b_size = 3,
        .a = { 0.7568359375f, 0.337890625f },
        .a_size = 3,
        .sample_time = 0.2
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 16,
        .max = 1.0,
        .min = -1.0,
        .scale = 1
};

digital_system plant = {
        .b = { 0.0264f },
        .b_size = 1,
        .a = { 1.0f, -0.9998f },
        .a_size = 2
};

