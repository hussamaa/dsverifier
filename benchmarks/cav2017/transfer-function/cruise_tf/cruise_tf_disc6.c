#include <dsverifier.h>

digital_system controller = {
        .b = { 0.265625f, 0.0107421875f },
	.b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.619140625f, 0.478515625f },
	.a_uncertainty = { 0.0, 0.0 },
        .a_size = 2,
        .sample_time = 2
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0,
        .scale = 1
};

digital_system plant = {
        .b = { 4.9938E-05 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 1,
        .a = { 1.0f, -0.9975f },
        .a_uncertainty = { 0.0, 0.0 },
        .a_size = 2,
};

