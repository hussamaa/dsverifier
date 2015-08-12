#include "../../../bmc/dsverifier.h"

digital_system ds = {
        .a = { 1.0, 1.0, -17.0, 15.0 },
        .a_size = 4,
        .b = { 1.0, 1.0, -17.0, 15.0 },
        .b_size = 4,
};

implementation impl = {
        .int_bits = 15,
        .frac_bits = 16,
        .delta = 0.25,
        .max = 1.0,
        .min = -1.0,
        .scale = 1
};
