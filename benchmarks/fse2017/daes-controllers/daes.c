#include <dsverifier.h>

hardware hw = {
	.clock = 16000000,
	.assembly = {
		.push = 2,
		.in = 1,
		.sbiw = 2,
		.cli = 1,
		.out = 1,
		.std = 2,
		.ldd = 2,
		.subi = 1,
		.sbci = 1,
		.lsl = 1,
		.rol = 1,
		.add = 1,
		.adc = 1,
		.adiw = 2,
		.rjmp = 2,
		.mov = 1,
		.sbc = 1,
		.ld = 2,
		.rcall = 4,
		.cp = 1,
		.cpc = 1,
		.ldi = 1,
		.brge = 2,
		.pop = 2,
		.ret = 5,
		.st = 2,
		.brlt = 2,
		.cpi = 1
	}
};

#if DS_ID == 1

	digital_system ds = {
		.b = { 0.15, 0.05, 0.4 },
		.b_size = 3,
		.a = { 1.0, 0.0, 0.3 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 4,
			.min = -1.0,
			.max = 1.0
		};

	#endif 

#endif

#if DS_ID == 2

	digital_system ds = {
		.b = { 2.000000, -4.000000, 2.000000 },
		.b_size = 3,
		.a = { 1.000000, 0.000000, -0.250000 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 6,
			.min = -1.0,
			.max = 1.0
		};

	#endif

#endif

#if DS_ID == 3

	digital_system ds = {
		.b = { 0.2, -0.4, 0.2 },
		.b_size = 3,
		.a = { 1.0, 0.0, -0.25 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 4,
			.min = -1.0,
			.max = 1.0
		};

	#endif

#endif

#if DS_ID == 4

	digital_system ds = {
		.b = { 1.0, -2.819, 2.637, -0.8187 },
		.b_size = 4,
		.a = { 1.0, -1.97, 1.033, -0.06068 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.min = -1.0,
			.max = 1.0
		};

	#endif

#endif

#if DS_ID == 5

	digital_system ds = {
		.b = { 0.0937, -0.3582, 0.5201, -0.3482, 0.1003, -0.0078 },
		.b_size = 6,
		.a = { 1.0000, 9.1122, -2.2473, -8.6564, 0.6569, 0.1355 },
		.a_size = 6,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.min = -1.0,
			.max = 1.0
		};

	#endif

#endif

#if DS_ID == 6

	digital_system ds = {
		.b = { 0.00937, -0.03582, 0.05201, -0.03482, 0.01003, -0.00078 },
		.b_size = 6,
		.a = { 1.0000, 9.1122, -2.2473, -8.6564, 0.6569, 0.1355 },
		.a_size = 6,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.min = -10.0,
			.max = 10.0
		};

	#endif

#endif

#if DS_ID == 7

	digital_system ds = {
		.b = { 0.1, -0.2819, 0.2637, -0.08187 },
		.b_size = 4,
		.a = { 1.0, -2.574, 2.181, -0.6068 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 8

	digital_system ds = {
		.b = { 0.10, -0.28, 0.26, -0.08 },
		.b_size = 4,
		.a = { 1.0, -2.57, 2.18, -0.60 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 8,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 9

	digital_system ds = {
		.b = { 0.1, -0.28, 0.26, -0.08 },
		.b_size = 4,
		.a = { 1.0, -2.57, 2.18, -0.60 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 11,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 10

	digital_system ds = {
		.b = { 0.2, -0.4, 0.2 },
		.b_size = 3,
		.a = { 1.0, 0.0, -0.25 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 12,
			.min = -1.0,
			.max = 1.0
		};

	#endif

#endif
