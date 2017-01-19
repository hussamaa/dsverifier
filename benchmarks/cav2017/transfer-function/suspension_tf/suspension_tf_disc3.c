#include <dsverifier.h>

digital_system controller = {
        .b = { 0.4931640625f, 0.3388671875f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.4541015625f, 0.25f },
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
        .b = { 0.2501f, 0.5f, 0.2495f, -3.2935E-4 },
        .b_uncertainty = { 0.0, 0.0, 0.0, 0.0 },
        .b_size = 4,
        .a = { 1.0f, -7.4795E-4, 3.2372E-6, -7.0249E-32, 8.3767E-113 },
        .a_uncertainty = { 0.0, 0.0, 0.0, 0.0, 0.0 },
        .a_size = 5,
};

