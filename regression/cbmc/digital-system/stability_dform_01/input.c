#include <dsverifier.h>

digital_system ds = {
    .a = { 1.0f, -1.97, 1.033, -0.06068 },
    .a_size = 4,
	.b = { 1.0f, -2.819, 2.637, -0.8187 },
	.b_size = 4
};

implementation impl = {
        .int_bits = 2,
        .frac_bits = 13,
};
