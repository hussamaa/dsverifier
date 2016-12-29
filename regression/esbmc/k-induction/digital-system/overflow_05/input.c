#include <dsverifier.h>

digital_system ds = { 
	.b = { 1.1000f, -0.6039f }, /* digital system numerator coefficients */
	.b_size = 2,
	.a = { 1.00000000f, 0.0340000f }, /* digital system denominator coefficients */
	.a_size = 2,
	.sample_time = 0.02
};

implementation impl = { 
	.int_bits = 3,
	.frac_bits = 5,
	.delta = 0.25,
	.max = 3.0,
	.min = -3.0,
};

