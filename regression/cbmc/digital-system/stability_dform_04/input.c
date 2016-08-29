#include <dsverifier.h>

digital_system ds = { 
	.b = {0.10f, -0.30f, 0.30f, -0.10f }, /* digital system numerator coefficients */
	.b_size = 4,
	.a = {1.000f, 1.800f, 1.140f, 0.272f }, /* digital system denominator coefficients */
	.a_size = 3,
	.sample_time = 0.02
};

implementation impl = { 
	.int_bits = 2,
	.frac_bits = 13,
	.delta = 0.25, 
	.max = 2.0,
	.min = -2.0,
};

