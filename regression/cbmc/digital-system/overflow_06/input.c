#include <dsverifier.h>

digital_system ds = { 
	.b = {0.2f, -0.4f, 0.2f}, /* digital system numerator coefficients */
	.b_size = 3,
	.a = {1.0f, 0.0f, -0.25f}, /* digital system denominator coefficients */
	.a_size = 3,
	.sample_time = 0.02
};

implementation impl = { 
	.int_bits = 3,
	.frac_bits = 4,
	.delta = 0.25,
	.max = 1.0,
	.min = -1.0,
};

