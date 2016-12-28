#include <dsverifier.h>

digital_system ds = {
		.b = { 0.10, -0.28, 0.26, -0.08 },
		.b_size = 4,
		.a = { 1.0, -2.57, 2.18, -0.60 },
		.a_size = 4,
		.sample_time = 0.01
	};

implementation impl = {
			.int_bits = 2,
			.frac_bits = 8,
			.min = -5.0,
			.max = 5.0
		};
