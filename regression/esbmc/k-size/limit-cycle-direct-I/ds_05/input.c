#include <dsverifier.h>

	digital_system ds = {
		.b = { 0.9411, -0.4229 },
		.b_size = 2,
		.a = { 1.00000000, 0.2480000 },
		.a_size = 2,
		.sample_time = 0.4
	};

implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.min = -3.0,
			.max = 3.0
		};
