#include <dsverifier.h>

	digital_system ds = {
		.b = { 1.1000, -0.6039 },
		.b_size = 2,
		.a = { 1.00000000, 0.0340000 },
		.a_size = 2,
		.sample_time = 0.3
	};

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};
