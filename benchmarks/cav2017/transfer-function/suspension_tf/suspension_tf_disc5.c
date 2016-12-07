#include <dsverifier.h>

digital_system controller = {
        .b = { 0.2890625f, 0.328125f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.53125f, 0.140625f },
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
        .b = { 0.3594f, 0.6235f, 0.1686f, -0.0954f },
        .b_uncertainty = { 0.0, 0.0, 0.0, 0.0 },
        .b_size = 4,
        .a = { 1.0f, -0.0237f, 0.0798f, -5.8793E-7, 3.8425E-23 },
        .a_uncertainty = { 0.0, 0.0, 0.0, 0.0, 0.0 },
        .a_size = 5,
};

