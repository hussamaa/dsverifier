#include <dsverifier.h>

digital_system ds = {
		.b = { 1.5000f, -1.357f },
		.b_size = 2,
		.a = { 1.0000000f, -0.8010000f },
		.a_size = 2,
		.sample_time = 0.025
	};

implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.min = -3.0,
			.max = 3.0
		};
