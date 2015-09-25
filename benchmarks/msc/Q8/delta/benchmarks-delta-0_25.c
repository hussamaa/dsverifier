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
		.b = { 0.10000000000000000555111512312578,  0.07240000000000024193980152631411,  -0.00159999999999893560698183136992,  -0.00447999999999915132775640813634 },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000,  1.70400000000000062527760746888816,  0.52800000000000579802872380241752,  0.01280000000001280113792745396495 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 8,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 2

	digital_system ds = {
		.b = { 0.10000000000000000555111512312578, 0.08000000000000007105427357601002, 0.00000000000000000000000000000000, -0.00000000000000177635683940025046  },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 1.72000000000000063948846218409017, 0.64000000000000767386154620908201, 0.64000000000001477928890381008387 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 3

	digital_system ds = {
		.b = { 0.10000000000000000555111512312578, 0.08000000000000007105427357601002, 0.00000000000000000000000000000000, -0.00000000000000177635683940025046  },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 1.72000000000000063948846218409017, 0.64000000000000767386154620908201, 0.64000000000001477928890381008387 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 4

	digital_system ds = {
		.b = { 0.10000000000000000555111512312578, 0.08000000000000007105427357601002, 0.00000000000000000000000000000000, -0.00000000000000177635683940025046  },
		.b_size = 4,
		.a = { 1.00000000000000000000000000000000, 1.72000000000000063948846218409017, 0.64000000000000767386154620908201, 0.64000000000001477928890381008387 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 5,
			.frac_bits = 8,
			.min = -10.0,
			.max = 10.0
		};

	#endif

#endif

#if DS_ID == 5

	digital_system ds = {
		.b = { 7.93599999999999994315658113919199, 20.06799999999999783995008328929543 },
		.b_size = 2,
		.a = {  1.00000000000000000000000000000000, 5.55600000000000004973799150320701 },
		.a_size = 2,
		.sample_time = 0.5
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 9,
			.frac_bits = 8,
			.min = -9.0,
			.max = 9.0
		};

	#endif

#endif

#if DS_ID == 6

	digital_system ds = {
		.b = { 1.26699999999999990407673067238647, 1.67079999999999939674921733967494 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 2.98280000000000011795009413617663 },
		.a_size = 2,
		.sample_time = 0.2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 7

	digital_system ds = {
		.b = {  1.43399999999999994138022429979173, 1.04000000000000003552713678800501 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 1.56800000000000006039613253960852 },
		.a_size = 2,
		.sample_time = 0.1
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 8

	digital_system ds = {
		.b = { 1.50000000000000000000000000000000, 0.57200000000000006394884621840902 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 0.79599999999999981881160238117445 },
		.a_size = 2,
		.sample_time = 0.05
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 9

	digital_system ds = {
		.b = { 1.56099999999999994315658113919199, 0.30399999999999938182781988871284 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 0.16000000000000014210854715202004 },
		.a_size = 2,
		.sample_time = 0.025
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 10

	digital_system ds = {
		.b = { 1.58400000000000007460698725481052, 0.12400000000000055422333389287814 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 0.16000000000000014210854715202004 },
		.a_size = 2,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 8,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 11

	digital_system ds = {
		.b = { 1.61099999999999998756550212419825, 25.20400000000000062527760746888816, 14.33600000000000207478478841949254 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 12.33600000000000029842794901924208,  35.40640000000000497948349220678210 },
		.a_size = 3,
		.sample_time = 0.4
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 11,
			.frac_bits = 8,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 12

	digital_system ds = {
		.b = { -1.69199999999999994848565165739274, 28.18399999999999749888957012444735,  13.16799999999999570832187600899488 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 12.18400000000000105160324892494828,  34.03968000000000415639078710228205 },
		.a_size = 3,
		.sample_time = 0.3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 14,
			.frac_bits = 8,
			.min = -12.0,
			.max = 12.0
		};

	#endif

#endif

#if DS_ID == 13

	digital_system ds = {
		.b = { -1.09899999999999997690736108779674, 3.12000000000000099475983006414026, 1.07200000000000272848410531878471 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 11.62720000000000020179413695586845, 29.46656000000000119598553283140063 },
		.a_size = 3,
		.sample_time = 0.2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 11,
			.frac_bits = 8,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 14

	digital_system ds = {
		.b = { -0.46029999999999998694377723040816, 0.34160000000000012576606422953773, 0.05759999999999987352339303470217 },
		.b_size = 3,
		.a = {  1.00000000000000000000000000000000, 10.37959999999999993747223925311118, 19.33119999999999905071490502450615 },
		.a_size = 3,
		.sample_time = 0.1
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 10,
			.frac_bits = 8,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 15

	digital_system ds = {
		.b = { -1.23900000000000010125233984581428, 0.34799999999999897681846050545573,  0.04799999999999826627572474535555 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 9.36919999999999930651028989814222,  11.12800000000000011368683772161603 },
		.a_size = 3,
		.sample_time = 0.05
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 12,
			.frac_bits = 8,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 16

	digital_system ds = {
		.b = { -2.81300000000000016697754290362354, 0.37199999999999988631316227838397,  0.01600000000000534328137291595340 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 8.73320000000000007389644451905042,  5.96160000000000067643668444361538 },
		.a_size = 3,
		.sample_time = 0.025
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 15,
			.frac_bits = 8,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 17

	digital_system ds = {
		.b = { -0.75300000000000000266453525910038, 0.05199999999999960209606797434390,  -0.00000000000000177635683940025046 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 8.30508000000000023987922759260982,  2.48112000000000065824679040815681 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 13,
			.frac_bits = 8,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 18

	digital_system ds = {
		.b = { -1.55299999999999993605115378159098, 0.05200000000000137845290737459436,  0.00000000000000355271367880050093 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 8.15492000000000061277205531951040,  1.25968000000000124316557048587129 },
		.a_size = 3,
		.sample_time = 0.005
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 15,
			.frac_bits = 8,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 19

	digital_system ds = { 
		.b = { 60.00000000000000000000000000000000, 40.00000000000000000000000000000000 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 4.00000000000000000000000000000000 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 8,
			.frac_bits = 8,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

#if DS_ID == 20

	digital_system ds = { 
		.b = { 110.00000000000000000000000000000000, 40.00000000000000000000000000000000 },
		.b_size = 2,
		.a = { 1.00000000000000000000000000000000, 4.00000000000000000000000000000000 },
		.a_size = 2,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 9, 
			.frac_bits = 8,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

#if DS_ID == 21

	digital_system ds = { 
		.b = {  135.00000000000000000000000000000000, 40.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 4.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.a_size = 3,
		.sample_time = 0.02
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 10,
			.frac_bits = 8,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif

#if DS_ID == 22

	digital_system ds = { 
		.b = {  2002.00000000000000000000000000000000, 16.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.b_size = 3,
		.a = { 1.00000000000000000000000000000000, 8.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.a_size = 3,	
		.sample_time = 0.001
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1
		implementation impl = { 
			.int_bits = 13,
			.frac_bits = 8,
			.max = 1.0,
			.min = -1.0
		};
	#endif

#endif
