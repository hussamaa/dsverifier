#include <dsverifier.h>

digital_system ds = {
		.b = { 0.0937, -0.3582, 0.5201, -0.3482, 0.1003, -0.0078 },
		.b_size = 6,
		.a = { 1.0000, 9.1122, -2.2473, -8.6564, 0.6569, 0.1355 },
		.a_size = 6,
		.sample_time = 0.01
	};

implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.min = -1.0,
			.max = 1.0
		};

