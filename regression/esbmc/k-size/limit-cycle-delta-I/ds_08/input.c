#include <dsverifier.h>

digital_system ds = {
		.b = { 1.4340, -1.174 },
		.b_size = 2,
		.a = { 1.0000000, -0.6080000 },
		.a_size = 2,
		.sample_time = 0.1
	};

implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

