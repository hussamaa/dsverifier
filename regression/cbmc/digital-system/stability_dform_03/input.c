#include <dsverifier.h>

digital_system ds = { 
	.b = {0.100f, -0.250f, 0.200f, -0.050f }, /* digital system numerator coefficients */
	.b_size = 4,
	.a = {1.000f, 1.500f, 0.680f, 0.096f }, /* digital system denominator coefficients */
	.a_size = 4,
	.sample_time = 0.02
};

implementation impl = { 
	.int_bits = 4,
	.frac_bits = 11,
	.delta = 0.25,
	.max = 5.0,
	.min = -5.0,
};

