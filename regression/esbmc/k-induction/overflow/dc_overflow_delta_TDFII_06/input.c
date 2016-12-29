#include <dsverifier.h>

digital_system ds = {
		.b = { 0.00937, -0.03582, 0.05201, -0.03482, 0.01003, -0.00078 },
		.b_size = 6,
		.a = { 1.0000, 9.1122, -2.2473, -8.6564, 0.6569, 0.1355 },
		.a_size = 6,
		.sample_time = 0.01
	};

implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.delta = 0.25,
			.min = -10.0,
			.max = 10.0
		};

