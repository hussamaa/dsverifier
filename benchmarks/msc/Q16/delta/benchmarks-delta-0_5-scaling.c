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
		.b = { 0.10000000000000000555111512312578, 0.03620000000000012096990076315706, -0.00039999999999973390174545784248, -0.00055999999999989391596955101704 },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 0.85200000000000031263880373444408, 0.13200000000000144950718095060438, 0.00160000000000160014224093174562 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 16,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 2

	digital_system ds = {
		.b = { 0.10000000000000000555111512312578, 0.04000000000000003552713678800501, 0.00000000000000000000000000000000, -0.00000000000000022204460492503131 },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 0.86000000000000031974423109204508,  0.16000000000000191846538655227050, 0.08000000000000184741111297626048 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 3

	digital_system ds = {
		.b = { 0.10000000000000000555111512312578, 0.04000000000000003552713678800501,  0.00000000000000000000000000000000, -0.00000000000000022204460492503131 },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 0.86000000000000031974423109204508,  0.16000000000000191846538655227050, 0.08000000000000184741111297626048 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 4

	digital_system ds = {
		.b = { 0.10000000000000000555111512312578, 0.04000000000000003552713678800501,  0.00000000000000000000000000000000, -0.00000000000000022204460492503131 },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 0.86000000000000031974423109204508,  0.16000000000000191846538655227050, 0.08000000000000184741111297626048 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 5,
			.frac_bits = 16,
			.min = -10.0,
			.max = 10.0
		};

	#endif

#endif

#if DS_ID == 5

	digital_system ds = {
		.b = { 7.93599999999999994315658113919199, 10.03399999999999891997504164464772 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 2.77800000000000002486899575160351 },
		.a_size = 2,
		.sample_time = 0.5
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 9,
			.frac_bits = 16,
			.min = -9.0,
			.max = 9.0,
			.scale = 10000
		};

	#endif

#endif

#if DS_ID == 6

	digital_system ds = {
		.b = { 1.26699999999999990407673067238647, 0.83539999999999969837460866983747 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 1.49140000000000005897504706808832 },
		.a_size = 2,
		.sample_time = 0.2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.min = -3.0,
			.max = 3.0,
			.scale = 100
		};

	#endif

#endif

#if DS_ID == 7

	digital_system ds = {
		.b = { 1.43399999999999994138022429979173, 0.52000000000000001776356839400250 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 0.78400000000000003019806626980426 },
		.a_size = 2,
		.sample_time = 0.1
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.min = -3.0,
			.max = 3.0,
			.scale = 100
		};

	#endif

#endif

#if DS_ID == 8

	digital_system ds = {
		.b = { 1.50000000000000000000000000000000, 0.28600000000000003197442310920451 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 0.39799999999999990940580119058723 },
		.a_size = 2,
		.sample_time = 0.05
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 9

	digital_system ds = {
		.b = { 1.56099999999999994315658113919199, 0.15199999999999969091390994435642 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 0.08000000000000007105427357601002 },
		.a_size = 2,
		.sample_time = 0.025
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 10

	digital_system ds = {
		.b = { 1.58400000000000007460698725481052, 0.06200000000000027711166694643907 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 0.08000000000000007105427357601002 },
		.a_size = 2,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 11

	digital_system ds = {
		.b = { 1.61099999999999998756550212419825, 12.60200000000000031263880373444408, 3.58400000000000051869619710487314 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 6.16800000000000014921397450962104,  8.85160000000000124487087305169553 },
		.a_size = 3,
		.sample_time = 0.4
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 11,
			.frac_bits = 16,
			.min = -5.0,
			.max = 5.0,
			.scale = 10000
		};

	#endif

#endif

#if DS_ID == 12

	digital_system ds = {
		.b = { -1.69199999999999994848565165739274, 14.09199999999999874944478506222367, 3.29199999999999892708046900224872 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 6.09200000000000052580162446247414,  8.50992000000000103909769677557051 },
		.a_size = 3,
		.sample_time = 0.3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 14,
			.frac_bits = 16,
			.min = -12.0,
			.max = 12.0,
			.scale = 10000
		};

	#endif

#endif

#if DS_ID == 13

	digital_system ds = {
		.b = { -1.09899999999999997690736108779674, 1.56000000000000049737991503207013, 0.26800000000000068212102632969618 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 5.81360000000000010089706847793423, 7.36664000000000029899638320785016 },
		.a_size = 3,
		.sample_time = 0.2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 11,
			.frac_bits = 16,
			.min = -4.0,
			.max = 4.0,
			.scale = 10000
		};

	#endif

#endif

#if DS_ID == 14

	digital_system ds = {
		.b = { -0.46029999999999998694377723040816, 0.17080000000000006288303211476887, 0.01439999999999996838084825867554 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 5.18979999999999996873611962655559,  4.83279999999999976267872625612654  },
		.a_size = 3,
		.sample_time = 0.1
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 10,
			.frac_bits = 16,
			.min = -3.0,
			.max = 3.0,
			.scale = 10000
		};

	#endif

#endif

#if DS_ID == 15

	digital_system ds = {
		.b = { -1.23900000000000010125233984581428, 0.17399999999999948840923025272787,  0.01199999999999956656893118633889 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 4.68459999999999965325514494907111,  2.78200000000000002842170943040401 },
		.a_size = 3,
		.sample_time = 0.05
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 12,
			.frac_bits = 16,
			.min = -4.0,
			.max = 4.0,
			.scale = 10000
		};

	#endif

#endif

#if DS_ID == 16

	digital_system ds = {
		.b = { -2.81300000000000016697754290362354, 0.18599999999999994315658113919199, 0.00400000000000133582034322898835  },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 4.36660000000000003694822225952521,  1.49040000000000016910917111090384 },
		.a_size = 3,
		.sample_time = 0.025
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 15,
			.frac_bits = 16,
			.min = -6.0,
			.max = 6.0,
			.scale = 1000
		};

	#endif

#endif

#if DS_ID == 17

	digital_system ds = {
		.b = { -0.75300000000000000266453525910038, 0.02599999999999980104803398717195, -0.00000000000000044408920985006262 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 4.15254000000000011993961379630491,  0.62028000000000016456169760203920 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 13,
			.frac_bits = 16,
			.min = -3.0,
			.max = 3.0,
			.scale = 1000
		};

	#endif

#endif

#if DS_ID == 18

	digital_system ds = {
		.b = { -1.55299999999999993605115378159098, 0.02600000000000068922645368729718, 0.00000000000000088817841970012523},
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 4.07746000000000030638602765975520,  0.31492000000000031079139262146782 },
		.a_size = 3,
		.sample_time = 0.005
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 15,
			.frac_bits = 16,
			.min = -3.0,
			.max = 3.0,
			.scale = 1000
		};

	#endif

#endif

#if DS_ID == 19

	digital_system ds = { 
		.b = { 60.00000000000000000000000000000000, 20.00000000000000000000000000000000 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 2.00000000000000000000000000000000 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 8,
			.frac_bits = 16,
			.max = 1.0,
			.min = -1.0,
			.scale = 1000
		};
	#endif

#endif

#if DS_ID == 20

	digital_system ds = { 
		.b = { 110.0, 20.0 },
		.b_size = 2,
		.a = { 1.0, 2.0 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 9, 
			.frac_bits = 16,
			.max = 1.0,
			.min = -1.0,
			.scale = 500
		};
	#endif

#endif

#if DS_ID == 21

	digital_system ds = { 
		.b = { 135.00000000000000000000000000000000, 20.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 2.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.a_size = 3,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 10,
			.frac_bits = 16,
			.max = 1.0,
			.min = -1.0,
			.scale = 500
		};
	#endif

#endif

#if DS_ID == 22

	digital_system ds = { 
		.b = { 2002.00000000000000000000000000000000, 8.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 4.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.a_size = 3,	
		.sample_time = 0.001
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 13,
			.frac_bits = 16,
			.max = 1.0,
			.min = -1.0,
			.scale = 1000000
		};
	#endif

#endif
