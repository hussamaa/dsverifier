#include <dsverifier.h>

/** PDPIBI */

/* pd */

#if DS_ID == 1

	digital_system ds = {
		.b = { 0.93, -0.87 },
		.b_size = 2,
		.a = { 1.0, 1.0 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 3

	/* carletta's implementation (not possible, unstable) */

	#if IMPLEMENTATION_ID == 1
		implementation impl = {
			.int_bits = 4,
			.frac_bits = 12,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 2
		implementation impl = {
			.int_bits = 8,
			.frac_bits = 8,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 3
		implementation impl = {
			.int_bits = 10,
			.frac_bits = 6,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

#endif

/* pi */

#if DS_ID == 2

	digital_system ds = {
		.b = { 0.1, -0.09998 },
		.b_size = 2,
		.a = { 1.0, -1.0 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 3

	/* carletta's implementation  (not possible, unstable) */

	#if IMPLEMENTATION_ID == 1
		implementation impl = {
			.int_bits = 4,
			.frac_bits = 12,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 2
		implementation impl = {
			.int_bits = 8,
			.frac_bits = 8,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 3
		implementation impl = {
			.int_bits = 10,
			.frac_bits = 6,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

#endif

/** PDPIBE */

/* pd */

#if DS_ID == 3

	digital_system ds = {
		.b = { 0.0096, -0.009 },
		.b_size = 2,
		.a = { 0.02, 0.0 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 3

	/* carletta's implementation (ok) */
	#if IMPLEMENTATION_ID == 1
		implementation impl = {
			.int_bits = 3,
			.frac_bits = 13,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 2
		implementation impl = {
			.int_bits = 4,
			.frac_bits = 12,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 3
		implementation impl = {
			.int_bits = 5,
			.frac_bits = 11,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

#endif

/* pi */

#if DS_ID == 4

	digital_system ds = {
		.b = { 0.1, -0.1 },
		.b_size = 2,
		.a = { 1.0, -1.0 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 3

	/* carletta's implementation (not possible, unstable) */
	#if IMPLEMENTATION_ID == 1
		implementation impl = {
			.int_bits = 4,
			.frac_bits = 12,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 2
		implementation impl = {
			.int_bits = 8,
			.frac_bits = 8,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 3
		implementation impl = {
			.int_bits = 10,
			.frac_bits = 6,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

#endif

/** PDPIFE */

/* pd */

#if DS_ID == 5

	digital_system ds = {
		.b = { 0.009, -0.0084 },
		.b_size = 2,
		.a = { 1.0 } ,
		.a_size = 1,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 3

	/* carletta's implementation (not possible) */

	#if IMPLEMENTATION_ID == 1
		implementation impl = {
			.int_bits = 4,
			.frac_bits = 12,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 2
		implementation impl = {
			.int_bits = 8,
			.frac_bits = 8,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 3
		implementation impl = {
			.int_bits = 10,
			.frac_bits = 6,
			.max = 1.0,
			.min = -1.0,
		};
	#endif


#endif

/* pi */

#if DS_ID == 6

	digital_system ds = {
		.b = { 0.1, -0.09996 },
		.b_size = 2,
		.a = { 1.0, -1.0 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 3

	/* carletta's implementation (not possible, stable) */

	#if IMPLEMENTATION_ID == 1
		implementation impl = {
			.int_bits = 4,
			.frac_bits = 12,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 2
		implementation impl = {
			.int_bits = 8,
			.frac_bits = 8,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

	#if IMPLEMENTATION_ID == 3
		implementation impl = {
			.int_bits = 10,
			.frac_bits = 6,
			.max = 1.0,
			.min = -1.0,
		};
	#endif

#endif
