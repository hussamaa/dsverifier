#include <dsverifier.h>

digital_system ds = {
		.b = { 0.2, -0.4, 0.2 },
		.b_size = 3,
		.a = { 1.0, 0.0, -0.25 },
		.a_size = 3,
		.sample_time = 0.01
	};	

implementation impl = {
			.int_bits = 3,
			.frac_bits = 4,
			.min = -1.0,
			.max = 1.0
		};		
