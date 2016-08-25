#include <dsverifier.h>

digital_system ds = {
        .a = { 1.0, -1.5, 0.56 },
        .a_uncertainty = { 0, 5, 0 },
        .a_size = 3,
        .b = { 1, -3.0 },
        .b_size = 2,
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 16,
        .delta = 0.25,
        .max = 1.0,
        .min = -1.0,
        .scale = 1
};
