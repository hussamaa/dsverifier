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
		.b = { 0.00937499999999999965305530480464,  0.08749999999999999444888487687422,  0.59999999999999997779553950749687 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.50000000000000000000000000000000, 1.30000000000000004440892098500626 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 1,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -1.0,
			.max = 1.0
		};

	#endif 

#endif

#if DS_ID == 2

	digital_system ds = {
		.b = { 0.01250000000000000069388939039072,  0.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000,  0.50000000000000000000000000000000,  0.75000000000000000000000000000000 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 5,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -1.0,
			.max = 1.0
		};

	#endif

#endif

#if DS_ID == 3

	digital_system ds = {
		.b = { 0.01250000000000000069388939039072,  0.00000000000000000000000000000000,  0.00000000000000000000000000000000 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000,  0.50000000000000000000000000000000,  0.75000000000000000000000000000000 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -1.0,
			.max = 1.0
		};

	#endif

#endif

#if DS_ID == 4

	digital_system ds = {
		.b = { 0.01562500000000000000000000000000, 0.01131250000000000310862446895044, -0.00024999999999997246646898929612, -0.00069999999999992290611317002913 },
		.b_size = 4,
		.a = { 0.01562500000000000000000000000000, 0.06437500000000000166533453693773, 0.02324999999999999289457264239900,  0.00231999999999998873789763820241 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -1.0,
			.max = 1.0
		};

	#endif

#endif

#if DS_ID == 5

	digital_system ds = {
		.b = { 0.00156250000000000008673617379884, 0.00113125000000000378030939884866, -0.00002499999999998336885909111516, -0.00006999999999998673949619387713 },
		.b_size = 4,
		.a = { 0.01562500000000000000000000000000, 0.02662500000000000976996261670138, 0.00825000000000009059419880941277, 0.00020000000000020001778011646820 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 6

	digital_system ds = {
		.b = { 0.00156250000000000008673617379884, 0.00125000000000000111022302462516, 0.00000000000000000000000000000000, -0.00000000000000002775557561562891 },
		.b_size = 4,
		.a = { 0.01562500000000000000000000000000, 0.02687500000000000999200722162641, 0.01000000000000011990408665951691, 0.01000000000000023092638912203256 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 7

	digital_system ds = {
		.b = { 0.00156250000000000008673617379884, 0.00125000000000000111022302462516, 0.00000000000000000000000000000000, -0.00000000000000002775557561562891 },
		.b_size = 4,
		.a = { 0.01562500000000000000000000000000, 0.02687500000000000999200722162641, 0.01000000000000011990408665951691, 0.01000000000000023092638912203256 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 8

	digital_system ds = {
		.b = { 0.01250000000000000069388939039072, 0.00000000000000000000000000000000, 0.00000000000000000000000000000000 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.50000000000000000000000000000000, 0.75000000000000000000000000000000 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 2,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -1.0,
			.max = 1.0
		};

	#endif

#endif

#if DS_ID == 9

	digital_system ds = {
		.b = { 0.00156250000000000008673617379884, 0.00000000000000000346944695195361, 0.00000000000000001387778780781446, 0.00000000000000000000000000000000 },
		.b_size = 4,
		.a = { 0.01562500000000000000000000000000, 0.29999999999999998889776975374843, 1.93500000000000005329070518200751, 4.21199999999999974420461512636393 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 6,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -2.0,
			.max = 2.0
		};

	#endif

#endif

#if DS_ID == 10

	digital_system ds = {
		.b = { 0.00156250000000000008673617379884, 0.00312500000000000277555756156289, 0.00000000000000001387778780781446, 0.00000000000000002775557561562891 },
		.b_size = 4,
		.a = { 0.01562500000000000000000000000000, 0.28125000000000000000000000000000, 1.66999999999999992894572642398998, 3.27599999999999980104803398717195 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 5,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -2.0,
			.max = 2.0
		};

	#endif

#endif

#if DS_ID == 11

	digital_system ds = {
		.b = { 0.00015625000000000000325260651746,  0.00000000000000000000000000000000,  0.00000000000000000000000000000000, -0.00000000000000000173472347597681 },
		.b_size = 4,
		.a = { 0.01562500000000000000000000000000, 0.29999999999999998889776975374843, 1.93500000000000005329070518200751, 4.21199999999999974420461512636393 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 3,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 12

	digital_system ds = {
		.b = { 0.00156250000000000008673617379884, 0.00312500000000000277555756156289, 0.00000000000000001387778780781446, 0.00000000000000002775557561562891 },
		.b_size = 4,
		.a = { 0.01562500000000000000000000000000, 0.28125000000000000000000000000000, 1.66999999999999992894572642398998, 3.27599999999999980104803398717195  },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 7,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 13

	digital_system ds = {
		.b = { 0.00156250000000000008673617379884, 0.00125000000000000111022302462516, 0.00000000000000000000000000000000, -0.00000000000000002775557561562891 },
		.b_size = 4,
		.a = { 0.01562500000000000000000000000000, 0.02687500000000000999200722162641, 0.01000000000000011990408665951691, 0.01000000000000023092638912203256 },
		.a_size = 4,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 5,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -10.0,
			.max = 10.0
		};

	#endif

#endif

#if DS_ID == 14

	digital_system ds = {
		.b = { 1.98399999999999998578914528479800, 5.01699999999999945998752082232386 },
		.b_size = 2,
		.a = { 0.25000000000000000000000000000000, 1.38900000000000001243449787580175 },
		.a_size = 2,
		.sample_time = 0.5
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 9,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -9.0,
			.max = 9.0
		};

	#endif

#endif

#if DS_ID == 15

	digital_system ds = {
		.b = { 0.23527500000000001190159082398168, 0.51819999999999999396038674603915 },
		.b_size = 2,
		.a = { 0.25000000000000000000000000000000, 1.24799999999999999822364316059975 },
		.a_size = 2,
		.sample_time = 0.4
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 16

	digital_system ds = {
		.b = { 0.27500000000000002220446049250313, 0.49610000000000009645617637943360 },
		.b_size = 2,
		.a = { 0.25000000000000000000000000000000, 1.03400000000000003019806626980426 },
		.a_size = 2,
		.sample_time = 0.3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 17

	digital_system ds = {
		.b = { 0.31674999999999997601918266809662, 0.41769999999999984918730433491874 },
		.b_size = 2,
		.a = { 0.25000000000000000000000000000000, 0.74570000000000002948752353404416 },
		.a_size = 2,
		.sample_time = 0.2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 18

	digital_system ds = {
		.b = { 0.35849999999999998534505607494793, 0.26000000000000000888178419700125 },
		.b_size = 2,
		.a = { 0.25000000000000000000000000000000, 0.39200000000000001509903313490213 },
		.a_size = 2,
		.sample_time = 0.1
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 19

	digital_system ds = {
		.b = { 0.37500000000000000000000000000000, 0.14300000000000001598721155460225 },
		.b_size = 2,
		.a = { 0.25000000000000000000000000000000, 0.19899999999999995470290059529361 },
		.a_size = 2,
		.sample_time = 0.05
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 20

	digital_system ds = {
		.b = { 0.39024999999999998578914528479800, 0.07599999999999984545695497217821 },
		.b_size = 2,
		.a = { 0.25000000000000000000000000000000, 0.04000000000000003552713678800501 },
		.a_size = 2,
		.sample_time = 0.025
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 21

	digital_system ds = {
		.b = { 0.39600000000000001865174681370263, 0.03100000000000013855583347321954},
		.b_size = 2,
		.a = { 0.25000000000000000000000000000000, 0.04000000000000003552713678800501 },
		.a_size = 2,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 4,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 22

	digital_system ds = {
		.b = { 0.17581250000000001043609643147647, 1.40242500000000003268496584496461, 0.92470000000000007744915819785092 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.76700000000000001509903313490213, 2.19189999999999995949906406167429 },
		.a_size = 3,
		.sample_time = 0.5
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 8,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 23

	digital_system ds = {
		.b = { 0.10068749999999999922284388276239, 1.57525000000000003907985046680551, 0.89600000000000012967404927621828 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.77100000000000001865174681370263, 2.21290000000000031121771826292388 },
		.a_size = 3,
		.sample_time = 0.4
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 11,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -5.0,
			.max = 5.0
		};

	#endif

#endif

#if DS_ID == 24

	digital_system ds = {
		.b = { -0.10574999999999999678035322858705, 1.76149999999999984368059813277796, 0.82299999999999973177011725056218 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.76150000000000006572520305780927, 2.12748000000000025977442419389263 },
		.a_size = 3,
		.sample_time = 0.3
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 14,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -12.0,
			.max = 12.0
		};

	#endif

#endif

#if DS_ID == 25

	digital_system ds = {
		.b = { -0.06868749999999999855671006798730, 0.19500000000000006217248937900877, 0.06700000000000017053025658242404 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.72670000000000001261213355974178, 1.84166000000000007474909580196254 },
		.a_size = 3,
		.sample_time = 0.2
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 11,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 26

	digital_system ds = {
		.b = { -0.02876874999999999918398607690051, 0.02135000000000000786037901434611, 0.00359999999999999209521206466889 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.64872499999999999609201495331945, 1.20819999999999994066968156403163 },
		.a_size = 3,
		.sample_time = 0.1
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 10,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 27

	digital_system ds = {
		.b = { -0.07743750000000000632827124036339, 0.02174999999999993605115378159098, 0.00299999999999989164223279658472 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.58557499999999995665689311863389, 0.69550000000000000710542735760100 },
		.a_size = 3,
		.sample_time = 0.05
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 12,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -4.0,
			.max = 4.0
		};

	#endif

#endif

#if DS_ID == 28

	digital_system ds = {
		.b = { -0.17581250000000001043609643147647, 0.02324999999999999289457264239900, 0.00100000000000033395508580724709 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.54582500000000000461852778244065, 0.37260000000000004227729277772596 },
		.a_size = 3,
		.sample_time = 0.025
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 15,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -6.0,
			.max = 6.0
		};

	#endif

#endif

#if DS_ID == 29

	digital_system ds = {
		.b = { -0.04706250000000000016653345369377, 0.00324999999999997513100424839649, -0.00000000000000011102230246251565 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.51906750000000001499245172453811, 0.15507000000000004114042440050980 },
		.a_size = 3,
		.sample_time = 0.01
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 13,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif

#if DS_ID == 30

	digital_system ds = {
		.b = { -0.09706249999999999600319711134944, 0.00325000000000008615330671091215, 0.00000000000000022204460492503131 },
		.b_size = 3,
		.a = { 0.06250000000000000000000000000000, 0.50968250000000003829825345746940, 0.07873000000000007769784815536696 },
		.a_size = 3,
		.sample_time = 0.005
	};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 

		implementation impl = {
			.int_bits = 15,
			.frac_bits = 16,
			.delta = 0.25,
			.min = -3.0,
			.max = 3.0
		};

	#endif

#endif
