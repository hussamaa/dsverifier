#include <dsverifier.h>

digital_system ds = {
	.b = { 2.000000, -4.000000, 2.000000 },
	.b_size = 3,
	.a = { 1.000000, 0.000000, -0.250000 },
	.a_size = 3,
	.sample_time = 0.01
};

implementation impl = {
	.int_bits = 2,
	.frac_bits = 6,
	.max_error = 8,
	.min = -1.0,
	.max = 1.0
};

