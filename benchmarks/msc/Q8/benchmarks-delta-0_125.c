#include "../../../bmc/dsverifier.h"

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
		.b = { 0.1, -0.2819, 0.2637, -0.08187 },
		.b_size = 4,
		.a = { 1.0, -2.574, 2.181, -0.6068 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 2

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
			.int_bits = 4,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 3

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
			.frac_bits = 8,
			.delta = 0.125,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 4

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
			.int_bits = 5,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -10.0,
			.max = 10.0
		};

	#endif

#endif

#if DS_ID == 5

	digital_system ds = {
		.b = { 7.936, -2.919 },
		.b_size = 2,
		.a = { 1.00000000, 0.3890000 },
		.a_size = 2,
		.sample_time = 0.5
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 9,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -9.0,
			.max = 9.0
		};

	#endif

#endif

#if DS_ID == 6

	digital_system ds = {
		.b = { 1.2670, -0.8493 },
		.b_size = 2,
		.a = { 1.0000000, -0.2543000 },
		.a_size = 2,
		.sample_time = 0.2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 7

	digital_system ds = {
		.b = { 1.4340, -1.174 },
		.b_size = 2,
		.a = { 1.0000000, -0.6080000 },
		.a_size = 2,
		.sample_time = 0.1
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 8

	digital_system ds = {
		.b = { 1.5000, -1.357 },
		.b_size = 2,
		.a = { 1.0000000, -0.8010000 },
		.a_size = 2,
		.sample_time = 0.05
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 9

	digital_system ds = {
		.b = { 1.5610, -1.485 },
		.b_size = 2,
		.a = { 1.0000000, -0.9600000 },
		.a_size = 2,
		.sample_time = 0.025
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 10

	digital_system ds = {
		.b = { 1.5840, -1.553 },
		.b_size = 2,
		.a = { 1.0000000, -0.9600000 },
		.a_size = 2,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 11

	digital_system ds = {
		.b = { 1.611, 3.079, -3.794 },
		.b_size = 3,
		.a = { 1.00000000, 1.0840000, 0.1289 },
		.a_size = 3,
		.sample_time = 0.4
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 11,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 12

	digital_system ds = {
		.b = { -1.692, 10.43, -7.915 },
		.b_size = 3,
		.a = { 1.00000000, 1.0460000, 0.08148 },
		.a_size = 3,
		.sample_time = 0.3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 14,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -12.0,
			.max = 12.0
		};

	#endif

#endif

#if DS_ID == 13

	digital_system ds = {
		.b = { -1.099, 2.978, -1.812 },
		.b_size = 3,
		.a = { 1.00000000, 0.9068000, -0.06514 },
		.a_size = 3,
		.sample_time = 0.2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 11,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 14

	digital_system ds = {
		.b = { -0.4603, 1.006, -0.5421 },
		.b_size = 3,
		.a = { 1.00000000, 0.5949000, -0.3867 },
		.a_size = 3,
		.sample_time = 0.1
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 10,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 15

	digital_system ds = {
		.b = { -1.239, 2.565, -1.323 },
		.b_size = 3,
		.a = { 1.00000000, 0.3423000, -0.6468 },
		.a_size = 3,
		.sample_time = 0.05
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 12,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 16

	digital_system ds = {
		.b = { -2.813, 5.719, -2.905 },
		.b_size = 3,
		.a = { 1.00000000, 0.18330, -0.8107 },
		.a_size = 3,
		.sample_time = 0.025
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 15,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 17

	digital_system ds = {
		.b = { -0.753, 1.519, -0.766 },
		.b_size = 3,
		.a = { 1.00000000, 0.0762700, -0.9212 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 13,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 18

	digital_system ds = {
		.b = { -1.553, 3.119, -1.566 },
		.b_size = 3,
		.a = { 1.00000000, 0.0387300, -0.96 },
		.a_size = 3,
		.sample_time = 0.005
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 15,
			.frac_bits = 8,
			.delta = 0.125,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 19

	digital_system ds = { 
		.b = { 60.0, -50.0 },
		.b_size = 2,
		.a = { 1.0, 0.0 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 8,
			.frac_bits = 8,
			.delta = 0.125,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

#if DS_ID == 20

	digital_system ds = { 
		.b = { 110.0, -100.0 },
		.b_size = 2,
		.a = { 1.0, 0.0 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 9, 
			.frac_bits = 8,
			.delta = 0.125,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

#if DS_ID == 21

	digital_system ds = { 
		.b = { 135.0, -260.0, 125.0 },
		.b_size = 3,
		.a = { 1.0, -1.0, 0.0 },
		.a_size = 3,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 10,
			.frac_bits = 8,
			.delta = 0.125,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

#if DS_ID == 22

	digital_system ds = { 
		.b = { 2002.0, -4000.0, 1998.0 },
		.b_size = 3,
		.a = { 1.0, 0.0, -1.0 },
		.a_size = 3,	
		.sample_time = 0.001
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 13,
			.frac_bits = 8,
			.delta = 0.125,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

