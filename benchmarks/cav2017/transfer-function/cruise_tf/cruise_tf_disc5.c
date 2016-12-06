#include <dsverifier.h>

digital_system controller = {
        .b = { 0.0078125f, 0.0234375f },
	.b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.546875f, 0.408203125f },
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
        .b = { 9.9750E-5 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 1,
        .a = { 1.0f, -0.9950f },
        .a_uncertainty = { 0.0, 0.0 },
        .a_size = 2,
};

