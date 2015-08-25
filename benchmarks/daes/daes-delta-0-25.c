#include "../bmc/dsverifier.h"

#if DS_ID == 1

	digital_system ds = {
		.b = { 0.15, 0.05, 0.4 },
		.b_size = 3,
		.a = { 1.0, 0.0, 0.3 },
		.a_size = 3 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 4,
			.delta = 0.25,
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
		.a_size = 3 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 6,
			.delta = 0.25,
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
		.a_size = 3 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 4,
			.delta = 0.25,
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
		.a_size = 4 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.delta = 0.25,
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
		.a_size = 6 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.delta = 0.25,
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
		.a_size = 6 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.delta = 0.25,
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
		.a_size = 4 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.delta = 0.25,
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
		.a_size = 4 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 8,
			.delta = 0.25,
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
		.a_size = 4 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 11,
			.delta = 0.25,
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
		.a_size = 3 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 12,
			.delta = 0.25,
			.min = -1.0,
			.max = 1.0
		};

	#endif

#endif

#if DS_ID == 11

	digital_system ds = {
		.b = { 0.10, -0.30, 0.30, -0.10 },
		.b_size = 4,
		.a = { 1.000, 1.800, 1.140, 0.272 },
		.a_size = 4 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.delta = 0.25,
			.min = -2.0,
			.max = 2.0
		};

	#endif

#endif

#if DS_ID == 12

	digital_system ds = {
		.b = { 0.100, -0.250, 0.200, -0.050 },
		.b_size = 4,
		.a = { 1.000, 1.500, 0.680, 0.096 },
		.a_size = 4 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.delta = 0.25,
			.min = -2.0,
			.max = 2.0
		};

	#endif

#endif

#if DS_ID == 13

	digital_system ds = {
		.b = { 0.0937, -0.3582, 0.5201, -0.3482, 0.1003, -0.0078 },
		.b_size = 6,
		.a = { 1.0000, 9.1122, -2.2473, -8.6564, 0.6569, 0.1355 },
		.a_size = 6 
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 13,
			.delta = 0.25,
			.min = -10.0,
			.max = 10.0
		};

	#endif

#endif

#if DS_ID == 14

	digital_system ds = {
		.b = { 0.010, -0.030, 0.030, -0.010 },
		.b_size = 4,
		.a = { 1.00, 1.800, 1.140, 0.272 },
		.a_size = 4
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 10,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 15

	digital_system ds = {
		.b = { 0.100, -0.250, 0.200, -0.050 },
		.b_size = 4,
		.a = { 1.000, 1.500, 0.680, 0.096 },
		.a_size = 4
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 11,
			.delta = 0.25,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 16

	digital_system ds = {
		.b = { 0.1, -0.28, 0.26, -0.08 },
		.b_size = 4,
		.a = { 1.0, -2.57, 2.18, -0.60 },
		.a_size = 4
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 5,
			.frac_bits = 10,
			.delta = 0.25,
			.min = -10.0,
			.max = 10.0
		};

	#endif

#endif

#if DS_ID == 17

	digital_system ds = {
		.b = { 7.936, -2.919 },
		.b_size = 2,
		.a = { 1.00000000, 0.3890000 },
		.a_size = 2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 5,
			.frac_bits = 10,
			.delta = 0.25,
			.min = -9.0,
			.max = 9.0
		};

	#endif

#endif

#if DS_ID == 18

	digital_system ds = {
		.b = { 0.9411, -0.4229 },
		.b_size = 2,
		.a = { 1.00000000, 0.2480000 },
		.a_size = 2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 19

	digital_system ds = {
		.b = { 1.1000, -0.6039 },
		.b_size = 2,
		.a = { 1.00000000, 0.0340000 },
		.a_size = 2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 20

	digital_system ds = {
		.b = { 1.2670, -0.8493 },
		.b_size = 2,
		.a = { 1.0000000, -0.2543000 },
		.a_size = 2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 21

	digital_system ds = {
		.b = { 1.4340, -1.174 },
		.b_size = 2,
		.a = { 1.0000000, -0.6080000 },
		.a_size = 2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 22

	digital_system ds = {
		.b = { 1.5000f, -1.357f },
		.b_size = 2,
		.a = { 1.0000000f, -0.8010000f },
		.a_size = 2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 23

	digital_system ds = {
		.b = { 1.5000f, -1.357f },
		.b_size = 2,
		.a = { 1.0000000f, -0.8010000f },
		.a_size = 2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 24

	digital_system ds = {
		.b = { 1.5840, -1.553 },
		.b_size = 2,
		.a = { 1.0000000, -0.9600000 },
		.a_size = 2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 25

	digital_system ds = {
		.b = { 2.81300000,-0.0163, -1.8720000 },
		.b_size = 3,
		.a = { 1.000, 1.068, 0.1239 },
		.a_size = 3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 26

	digital_system ds = {
		.b = { 1.611, 3.079, -3.794 },
		.b_size = 3,
		.a = { 1.00000000, 1.0840000, 0.1289 },
		.a_size = 3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 27

	digital_system ds = {
		.b = { -1.692, 10.43, -7.915 },
		.b_size = 3,
		.a = { 1.00000000, 1.0460000, 0.08148 },
		.a_size = 3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 6,
			.frac_bits = 7,
			.delta = 0.25,
			.min = -12.0,
			.max = 12.0
		};

	#endif

#endif

#if DS_ID == 28

	digital_system ds = {
		.b = { -1.099, 2.978, -1.812 },
		.b_size = 3,
		.a = { 1.00000000, 0.9068000, -0.06514 },
		.a_size = 3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 29

	digital_system ds = {
		.b = { -0.4603, 1.006, -0.5421 },
		.b_size = 3,
		.a = { 1.00000000, 0.5949000, -0.3867 },
		.a_size = 3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 7,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 30

	digital_system ds = {
		.b = { -1.239, 2.565, -1.323 },
		.b_size = 3,
		.a = { 1.00000000, 0.3423000, -0.6468 },
		.a_size = 3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 31

	digital_system ds = {
		.b = { -2.813, 5.719, -2.905 },
		.b_size = 3,
		.a = { 1.00000000, 0.18330, -0.8107 },
		.a_size = 3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 32

	digital_system ds = {
		.b = { -0.753, 1.519, -0.766 },
		.b_size = 3,
		.a = { 1.00000000, 0.0762700, -0.9212 },
		.a_size = 3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 33

	digital_system ds = {
		.b = { -1.553, 3.119, -1.566 },
		.b_size = 3,
		.a = { 1.00000000, 0.0387300, -0.96 },
		.a_size = 3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 5,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif
