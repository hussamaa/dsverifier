#include<dsverifier.h>

#if DS_ID == 1

	digital_system ds = { 
		.b = { 1.5, -0.5 },
		.b_size = 2,
		.a = { 1.0 },
		.a_size = 1,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 3,
			.frac_bits = 5,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

#endif

#if DS_ID == 2

	digital_system ds = { 
		.b = { 60.0, -50.0 },
		.b_size = 2,
		.a = { 1.0 },
		.a_size = 1,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 3,
			.frac_bits = 5,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

#endif

#if DS_ID == 3

	digital_system ds = { 
		.b = { 110.0, -100.0 },
		.b_size = 2,
		.a = { 1.0 },
		.a_size = 1,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 3,
			.frac_bits = 5,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

#endif

#if DS_ID == 4

	digital_system ds = { 
		.b = { 135.0, -260.0, 125.0 },
		.b_size = 3,
		.a = { 1.0, -1.0 },
		.a_size = 1,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 3,
			.frac_bits = 5,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

#endif

#if DS_ID == 5

	digital_system ds = { 
		.b = { 2002.0, -4000.0, 1998.0 },
		.b_size = 3,
		.a = { 1.0, -1.0 },
		.a_size = 2,	
		.sample_time = 0.001
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 3,
			.frac_bits = 5,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

#endif
