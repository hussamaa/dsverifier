#include "../../../../bmc/dsverifier.h"

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
		.b = { 0.10000000000000000555111512312578, 0.14480000000000048387960305262823,  -0.00639999999999574242792732547969, -0.03583999999999321062205126509070 },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 3.40800000000000125055521493777633, 2.11200000000002319211489520967007, 0.10240000000010240910341963171959 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 4,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 2

	digital_system ds = {
		.b = { 0.10000000000000000555111512312578, 0.16000000000000014210854715202004,  0.00000000000000000000000000000000, -0.00000000000001421085471520200372 },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 3.44000000000000127897692436818033, 2.56000000000003069544618483632803, 5.12000000000011823431123048067093 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 4,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 3

	digital_system ds = {
		.b = { 0.10000000000000000555111512312578, 0.16000000000000014210854715202004,  0.00000000000000000000000000000000, -0.00000000000001421085471520200372 },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 3.44000000000000127897692436818033, 2.56000000000003069544618483632803, 5.12000000000011823431123048067093 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 4,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 4

	digital_system ds = {
		.b = { 0.10000000000000000555111512312578, 0.16000000000000014210854715202004,  0.00000000000000000000000000000000, -0.00000000000001421085471520200372 },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 3.44000000000000127897692436818033, 2.56000000000003069544618483632803, 5.12000000000011823431123048067093 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 5,
			.frac_bits = 4,
			.min = -10.0,
			.max = 10.0
		};

	#endif

#endif

#if DS_ID == 5

	digital_system ds = {
		.b = { 7.93599999999999994315658113919199, 40.13599999999999567990016657859087 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 11.11200000000000009947598300641403 },
		.a_size = 2,
		.sample_time = 0.5
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 9,
			.frac_bits = 4,
			.min = -9.0,
			.max = 9.0
		};

	#endif

#endif

#if DS_ID == 6

	digital_system ds = {
		.b = { 1.26699999999999990407673067238647, 3.34159999999999879349843467934988 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 5.96560000000000023590018827235326 },
		.a_size = 2,
		.sample_time = 0.2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 4,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 7

	digital_system ds = {
		.b = { 1.43399999999999994138022429979173, 2.08000000000000007105427357601002 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 3.13600000000000012079226507921703 },
		.a_size = 2,
		.sample_time = 0.1
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 4,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 8

	digital_system ds = {
		.b = { 1.50000000000000000000000000000000, 1.14400000000000012789769243681803 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 1.59199999999999963762320476234891 },
		.a_size = 2,
		.sample_time = 0.05
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 4,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 9

	digital_system ds = {
		.b = { 1.56099999999999994315658113919199, 0.60799999999999876365563977742568 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 0.32000000000000028421709430404007 },
		.a_size = 2,
		.sample_time = 0.025
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 4,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 10

	digital_system ds = {
		.b = { 1.58400000000000007460698725481052, 0.24800000000000110844666778575629},
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 0.32000000000000028421709430404007 },
		.a_size = 2,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 4,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 11

	digital_system ds = {
		.b = { 1.61099999999999998756550212419825, 50.40800000000000125055521493777633,  57.34400000000000829913915367797017 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 24.67200000000000059685589803848416, 141.62560000000001991793396882712841 },
		.a_size = 3,
		.sample_time = 0.4
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 11,
			.frac_bits = 4,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 12

	digital_system ds = {
		.b = { -1.69199999999999994848565165739274, 56.36799999999999499777914024889469,  52.67199999999998283328750403597951 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 24.36800000000000210320649784989655,  136.15872000000001662556314840912819 },
		.a_size = 3,
		.sample_time = 0.3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 14,
			.frac_bits = 4,
			.min = -12.0,
			.max = 12.0
		};

	#endif

#endif

#if DS_ID == 13

	digital_system ds = {
		.b = { -1.09899999999999997690736108779674, 6.24000000000000198951966012828052,  4.28800000000001091393642127513885 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 23.25440000000000040358827391173691,  117.86624000000000478394213132560253 },
		.a_size = 3,
		.sample_time = 0.2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 11,
			.frac_bits = 4,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 14

	digital_system ds = {
		.b = { -0.46029999999999998694377723040816, 0.68320000000000025153212845907547, 0.23039999999999949409357213880867 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 20.75919999999999987494447850622237, 77.32479999999999620285962009802461 },
		.a_size = 3,
		.sample_time = 0.1
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 10,
			.frac_bits = 4,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 15

	digital_system ds = {
		.b = { -1.23900000000000010125233984581428, 0.69599999999999795363692101091146,  0.19199999999999306510289898142219 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 18.73839999999999861302057979628444, 44.51200000000000045474735088646412 },
		.a_size = 3,
		.sample_time = 0.05
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 12,
			.frac_bits = 4,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 16

	digital_system ds = {
		.b = { -2.81300000000000016697754290362354, 0.74399999999999977262632455676794, 0.06400000000002137312549166381359 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 17.46640000000000014779288903810084,  23.84640000000000270574673777446151 },
		.a_size = 3,
		.sample_time = 0.025
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 15,
			.frac_bits = 4,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 17

	digital_system ds = {
		.b = { -0.75300000000000000266453525910038, 0.10399999999999920419213594868779,  -0.00000000000000710542735760100186 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 16.61016000000000047975845518521965,  9.92448000000000263298716163262725 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 13,
			.frac_bits = 4,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 18

	digital_system ds = {
		.b = { -1.55299999999999993605115378159098, 0.10400000000000275690581474918872,  0.00000000000001421085471520200372 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 16.30984000000000122554411063902080,  5.03872000000000497266228194348514 },
		.a_size = 3,
		.sample_time = 0.005
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 15,
			.frac_bits = 4,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 19

	digital_system ds = { 
		.b = { 60.00000000000000000000000000000000, 80.00000000000000000000000000000000 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 8.00000000000000000000000000000000 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 8,
			.frac_bits = 4,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

#if DS_ID == 20

	digital_system ds = { 
		.b = { 110.00000000000000000000000000000000, 80.00000000000000000000000000000000 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 8.00000000000000000000000000000000 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 9, 
			.frac_bits = 4,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

#if DS_ID == 21

	digital_system ds = { 
		.b = { 135.00000000000000000000000000000000, 80.00000000000000000000000000000000, 0.00000000000000000000000000000000 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 8.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.a_size = 3,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 10,
			.frac_bits = 4,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

#if DS_ID == 22

	digital_system ds = { 
		.b = { 2002.00000000000000000000000000000000, 32.00000000000000000000000000000000, 0.00000000000000000000000000000000 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 16.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.a_size = 3,	
		.sample_time = 0.001
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 13,
			.frac_bits = 4,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

