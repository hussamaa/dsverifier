#include<dsverifier.h>

#define SCHEMA_COUNT 8

#if SCHEMA_ID == 1

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.000163478496954612, 0.000490435490863836, 0.000490435490863836, 0.000163478496954612 },
			.b_uncertainty = { 0, 0, 0, 0 },
			.b_size = 4,
			.a = { 1.0,  2.85333563470071, 2.69002972632681, 0.839001811241234 },
			.a_uncertainty = { 0, 0, 0, 0 },
			.a_size = 4,
			.sample_time = 0.5
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 7

		digital_system control = { 
			.b = { -46722.9388629856, -262083.224184467, -626954.386010062, -828835.641678927, -653680.520872611, -307385.485152568, -79742.6078378329, -8796.10256753001 },
			.b_size = 8,
			.a = { 1.0, 4.39058739052463, 6.78019057140763, 2.73084222522736, -4.03915841957491, -5.56020614578946, -2.63698578163679, -0.457177157857307 },
			.a_size = 8,
			.sample_time = 0.5
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 2

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.000135296191782727, 0.000405888575348181, 0.000405888575348181, 0.000135296191782727 },
			.b_uncertainty = { 0, 0, 0, 0 },
			.b_size = 4,
			.a = { 1.0, 2.78314357832298, 1.93548684743101, 0.391079311955965 },
			.a_uncertainty = { 0, 0, 0, 0 },
			.a_size = 4,
			.sample_time = 0.1
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -28648.8858565043, -71100.1777349597, -63745.5345619543, -24288.0140094144, -2202.84628488319, 1076.19122855692, 309.052070556507, 23.7858830318072 },
			.b_size = 8,
			.a = { 1.0, 2.63110301693050, 1.54117385066207, -1.49326905489044, -2.25410744443172, -1.04757744103050, -0.212933451493943 -0.0164276751313222 },
			.a_size = 4,
			.sample_time = 0.1
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 3

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.000146919567623741, 0.000440758702871222,	0.000440758702871222, 0.000146919567623741 },
			.b_uncertainty = { 0, 0, 0, 0 },
			.b_size = 4,
			.a = { 1.0, 4.28788109958098, 1.28031526722658, 0.0664021473355693 },
			.a_uncertainty = { 0, 0, 0, 0 },
			.a_size = 4,
			.sample_time = 0.05
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -34273.6501085805, -19130.9645729250, 18120.6214868453, 2180.72915745924, -792.939398945145, 7.49199674729126, 3.15099827864785, -0.0736036832762937 },
			.b_size = 8,
			.a = { 1.0, 1.43352916367902, -0.635729660923281, -1.55026380548076, -0.333959013687237, 0.126493126889267, -0.0135202306539328, 3.79393476138021e-05 },
			.a_size = 8,
			.sample_time = 0.05
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

	#endif

#endif

//

#if SCHEMA_ID == 4

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.00883950571473951, 0.0265185171442185, 0.0265185171442185, 0.00883950571473951 },
			.b_uncertainty = { 0, 0, 0, 0 },
			.b_size = 4,
			.a = { 1.0, 488.620224835879, -90.2588471106943, -0.186697120598673 },
			.a_uncertainty = { 0, 0, 0, 0 },
			.a_size = 4,
			.sample_time = 0.03
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -45456.4327794820, 37928.1358865330, 25543.7662474832, -38701.0877810658,	16110.0090474469, -2847.85796600340, 182.232432139165, 0.384808123430819 },
			.b_size = 8,
			.a = { 1.0, 0.477366979853768, -1.49224375355836, -0.623599014821537, 0.646153752361363, 0.104133295454919, -0.124372938392141, 0.0182430318758402 },
			.a_size = 8,
			.sample_time = 0.03
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 5

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { -4.15622356143379e-06, -1.24686706843014e-05, -1.24686706843014e-05, -4.15622356143379e-06 },
			.b_uncertainty = { 0, 0, 0, 0 },
			.b_size = 4,
			.a = { 1.0, -3.13269459816456, 2.57307561263557, -0.628067890434017 },
			.a_uncertainty = { 0, 0, 0, 0 },
			.a_size = 4,
			.sample_time = 0.01
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -103936.565284686, 325443.019850986, -305547.710839180, -67884.9749823000,	328486.574723286, -247468.334712323, 80941.2733340117, -10146.1382229314 },
			.b_size = 8,
			.a = { 1.0, -1.64958891936817, -0.128811257947689, 1.03486242665554,	0.0875311092704659, -0.361050383559763, -0.0486851306838554, 0.0658307053887780 },
			.a_size = 8,
			.sample_time = 0.01
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 6

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { -5.23276352655263e-07, -1.56982905796579e-06, -1.56982905796579e-06, -5.23276352655263e-07 },
			.b_uncertainty = { 0, 0, 0, 0 },
			.b_size = 4,
			.a = { 1.0, -2.91022143320193, 2.68156090070522, -0.794969597702854 },
			.a_uncertainty = { 0, 0, 0, 0 },
			.a_size = 4,
			.sample_time = 0.005
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -159141.759428515, 632407.618367344, -846673.623630096, 167595.804971356,	687672.296322758, -749411.265417325, 318140.884548299, -50594.3601089297 },
			.b_size = 8,
			.a = { 1.0, -3.07551896140029, 3.29806425463714, -1.39488055019026,	0.259022232781851, -0.108217305190926, -0.0113306906473841, 0.0328644757931582 },
			.a_size = 8,
			.sample_time = 0.005
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 7

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { -4.43746079625357e-09, -1.33123823887607e-08, -1.33123823887607e-08, -4.43746079625357e-09 },
			.b_uncertainty = { 0, 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -2.95981646428031, 2.91494655257630, -0.955330475291959 },
			.a_uncertainty = { 0, 0, 0, 0 },
			.a_size = 4,
			.sample_time = 0.001
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -148496.867233430, 709359.050165142, -1206938.28913247, 585624.426432380,	736818.437145795, -1176777.30255828, 618616.719018390, -118206.174240954 },
			.b_size = 8,
			.a = { 1.0, -5.74813054330414, 14.0904227202400, -19.0956238772609,	15.4508595260727, -7.46080514819814, 1.98820008121862, -0.224922758451700 },
			.a_size = 8,
			.sample_time = 0.001
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 8

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { -5.60475478687645e-10, -1.68142643606293e-09, -1.68142643606293e-09, -5.60475478687645e-10 },
			.b_uncertainty = { 0, 0, 0, 0 },
			.b_size = 4,
			.a = { 1.0, -2.97853355473022, 2.95592124476812, -0.977413000007416 }, 
			.a_uncertainty = { 0, 0, 0, 0 },
			.a_size = 4,
			.sample_time = 0.0005
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -97152.2251983758, 474804.833149409, -831040.759909910, 432455.869535647,	484792.184946590, -820580.228953213, 443400.800159515, -86680.4737340240 },
			.b_size = 8,
			.a = { 1.0, -6.32487226166685, 17.1237618618006, -25.7241466902230, 23.1572445501548, -12.4913754686778, 3.73802837786626, -0.478640369250650 },
			.a_size = 8,
			.sample_time = 0.0005
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.max = 3.0,
				.min = -3.0,
				.scale = 1
			};
		#endif

	#endif

#endif
