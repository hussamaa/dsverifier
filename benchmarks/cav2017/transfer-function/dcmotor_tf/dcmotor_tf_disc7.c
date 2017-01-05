#include <dsverifier.h>

digital_system controller = {
        .b = { 0.84375f, 0.84375f },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 0.2734375f, 0.2255859375f, 0.0f },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
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
        .b = { 0.0018f, 1.9971E-4 },
        .b_uncertainty = { 0.0, 0.0 },
        .b_size = 2,
        .a = { 1.0f, -0.9990f, 4.5355E-5 },
        .a_uncertainty = { 0.0, 0.0, 0.0 },
        .a_size = 3,
};

