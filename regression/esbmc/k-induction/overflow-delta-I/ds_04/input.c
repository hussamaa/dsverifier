#include <dsverifier.h>

digital_system ds = {
		.b = { 7.936, -2.919 },
		.b_size = 2,
		.a = { 1.00000000, 0.3890000 },
		.a_size = 2,
		.sample_time = 0.5
	};

implementation impl = {
			.int_bits = 5,
			.frac_bits = 10,
			.delta = 0.25,
			.min = -9.0,
			.max = 9.0
		};
