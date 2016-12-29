#include <dsverifier.h>

digital_system ds = { 
	.b = { 2.000000f, -4.000000f, 2.000000f }, /* digital system numerator coefficients */
	.b_size = 3,
	.a = { 1.000000f, 0.000000f, -0.250000f }, /* digital system denominator coefficients */
	.a_size = 3,
	.sample_time = 0.02
};

implementation impl = { 
	.int_bits = 2,
	.frac_bits = 6,
	.max = 1.0,
	.min = -1.0,
};

