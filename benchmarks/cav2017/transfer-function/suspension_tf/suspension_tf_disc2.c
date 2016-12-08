#include <dsverifier.h>

digital_system controller = {
        .b = { 0.015625f, 0.000976562f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.125f },
        .a_uncertainty = { 0.0 },
        .a_size = 1,
        .sample_time = 1.5,
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0,
        .scale = 1,
};

digital_system plant = {
        .b = { 0.25f, 0.5f, 0.25f, -5.7065E-10 },
        .b_uncertainty = { 0.0, 0.0, 0.0, 0.0 },
        .b_size = 4,
        .a = { 1.0f, 6.8455E-9, 3.3925E-17, -3.4667E-94 },
        .a_uncertainty = { 0.0, 0.0, 0.0, 0.0 },
        .a_size = 4,
};

