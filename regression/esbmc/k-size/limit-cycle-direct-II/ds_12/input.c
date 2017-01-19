#include <dsverifier.h>

digital_system ds = {
		.b = { 2.81300000,-0.0163, -1.8720000 },
		.b_size = 3,
		.a = { 1.000, 1.068, 0.1239 },
		.a_size = 3,
		.sample_time = 0.5
	};

implementation impl = {
			.int_bits = 4,
			.frac_bits = 5,
			.min = -5.0,
			.max = 5.0
		};
