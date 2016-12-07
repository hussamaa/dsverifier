#include <dsverifier.h>

digital_system controller = {
        .b = { 0.0546875f },
        .b_uncertainty = { 0.0 },
        .b_size = 1,
        .a = { 0.126953125f },
        .a_uncertainty = { 0.0 },
        .a_size = 1,
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
        .b = { 0.25f, 0.5f, 0.25f, -4.3341E-7 },
        .b_uncertainty = { 0.0, 0.0, 0.0, 0.0 },
        .b_size = 4,
        .a = { 1.0f, 5.9150E-6, 1.0480E-11, -4.9349E-63, 7.0168E-225 },
        .a_uncertainty = { 0.0, 0.0, 0.0, 0.0, 0.0 },
        .a_size = 5,
};

