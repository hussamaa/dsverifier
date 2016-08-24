#include <dsverifier.h>

digital_system ds = {
    .a = { 1.0, 0.0, -0.25 },
    .a_size = 3,
	.b = { 0.2f, -0.4f, 0.2f },
	.b_size = 3
};

implementation impl = {
    .int_bits = 3,
    .frac_bits = 8,
	.min = -10,
	.max = 10
};
