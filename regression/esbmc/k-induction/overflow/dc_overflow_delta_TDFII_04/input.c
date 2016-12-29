#include <dsverifier.h>

digital_system ds = {
		.b = { 1.0, -2.819, 2.637, -0.8187 },
		.b_size = 4,
		.a = { 1.0, -1.97, 1.033, -0.06068 },
		.a_size = 4,
		.sample_time = 0.01
	};

implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.delta = 0.25,
			.min = -1.0,
			.max = 1.0
		};

