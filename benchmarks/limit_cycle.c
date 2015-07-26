#include "../dsverifier.h"

#if DS_ID == 1

	digital_system ds = { 
		.b = {0.10f, -0.28f, 0.26f, -0.08f},
		.b_size = 4,
		.a = {1.0f, -2.57f, 2.18f, -0.60f},
		.a_size = 4,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 2,
			.frac_bits = 8,
			.max = 5.0,
			.min = -5.0,
		};
	#endif

#endif

#if DS_ID == 2

	digital_system ds = { 
		.b = {0.10f, -0.28f, 0.26f, -0.08f},
		.b_size = 4,
		.a = {1.0f, -2.57f, 2.18f, -0.60f},
		.a_size = 4,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 4,
			.frac_bits = 11,
			.max = 6.0,
			.min = -6.0,
		};
	#endif

#endif

#if DS_ID == 3

	digital_system ds = { 
		.b = {0.010f, -0.030f, 0.030f, -0.010f },
		.b_size = 4,
		.a = {1.000f, 1.800f, 1.140f, 0.272f },
		.a_size = 4,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 3,
			.frac_bits = 10,
			.max = 3.0,
			.min = -3.0,
		};
	#endif

#endif

#if DS_ID == 4

	digital_system ds = { 
		.b = {0.100f, -0.250f, 0.200f, -0.050f },
		.b_size = 4,
		.a = {1.000f, 1.500f, 0.680f, 0.096f },
		.a_size = 4,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 4,
			.frac_bits = 11,
			.max = 5.0,
			.min = -5.0,
		};
	#endif

#endif
