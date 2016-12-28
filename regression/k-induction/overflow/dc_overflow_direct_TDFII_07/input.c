#include <dsverifier.h>

digital_system ds = {
		.b = { 0.1, -0.2819, 0.2637, -0.08187 },
		.b_size = 4,
		.a = { 1.0, -2.574, 2.181, -0.6068 },
		.a_size = 4,
		.sample_time = 0.01
	};


implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.min = -4.0,
			.max = 4.0
		};

