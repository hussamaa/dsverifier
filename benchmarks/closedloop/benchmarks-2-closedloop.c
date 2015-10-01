#include<dsverifier.h>

#define SCHEMA_COUNT 7

#if SCHEMA_ID == 1

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.171428571428571, -0.114285714285714, -0.285714285714286 },
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -1.88571428571429, 0.771428571428572 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.5
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -2.70561932258292, 4.91891416097458, -2.98975424265897, 0.607457221322442 },
			.b_size = 4,
			.a = { 1.0,	-0.246954439828182, -0.800014083515246, 0.356805858742342 },
			.a_size = 4,
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
			.b = { 0.0463980463980460, -0.00488400488400489, -0.0512820512820513 },
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -1.95604395604396, 0.951159951159951 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.1
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -10.6541798765226, 28.9820624061405, -26.2822459536125, 7.94546415262250 },
			.b_size = 4,
			.a = { 1.0, -0.976750653540241, -0.695199955503643, 0.688265939892838 },
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
			.b = { 0.0240815066378512, -0.00123494905835134, -0.0253164556962025 },
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -1.97653596789132, 0.975301018832973 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.05
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -19.2414736482723, 54.9701308152594, -52.3486145801513, 16.6178011176798 },
			.b_size = 4,
			.a = { 1.0, -1.20633950872401, -0.423011266643906, 0.633303983755908 },
			.a_size = 4,
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

#if SCHEMA_ID == 4

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.0146666501222221, -0.000446700003722501, -0.0151133501259446 },
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0,	-1.98555669987964, 0.985109999875917 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.03
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -28.8602335012427, 84.0786290054145, -81.6496235908929, 26.4305091092668 },
			.b_size = 4,
			.a = { 1.0, -1.39914676903959, -0.111714450559205, 0.512179344931653 },
			.a_size = 4,
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
			.b = { 0.00496265539470567, -4.98759336151326e-05, -0.00501253132832080 },
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -1.99506228257210, 0.995012406638487 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.01
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -58.8544737007610, 174.846413073101, -173.146281000398, 57.1542857242685 },
			.b_size = 4,
			.a = { 1.0, -1.92141324780054, 0.863510897744980, 0.0580048403364478 },
			.a_size = 4,
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
			.b = { 0.00249064447766700, -1.24844334720149e-05, -0.00250312891113892 },
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -1.99751559773907, 0.997503113305597 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.005
		};

	#endif
	
	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -79.8561004850143, 238.400671160303, -237.238792985947, 78.6942127596070 },
			.b_size = 4,
			.a = { 1.0, -2.26995707001617, 1.54695565228205, -0.276981072005969 },
			.a_size = 4,
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
			.b = { 0.000499625156164104, -4.99875093710924e-07, -0.000500125031257814 },
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -1.99950062478138, 0.999500124906289 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.001
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -111.957457802305, 335.544346474481, -335.216643366135, 111.629754586207 },
			.b_size = 4,
			.a = { 1.0, -2.79568196431083, 2.59175994708314, -0.796077785225516 },
			.a_size = 4,
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
			.b = { 4.99996250015625e-06, -4.99998750011460e-11, -5.00001250003125e-06 },
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -1.99999500006250, 0.999995000012500 }, 
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.00001
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -124.360611914036, 373.078190345452, -373.074544984800, 124.356966553384 },
			.b_size = 4,
			.a = { 1.0, -2.99773153180047, 2.99546310762128, -0.997731575820593 },
			.a_size = 4,
			.sample_time = 0.00001
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

#if SCHEMA_ID == 9

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 4.99999625000156e-07, -4.99999874981061e-13, -5.00000125000031e-07 },
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -1.99999950000063, 0.999999500000125 }, 
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.000001
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -124.486047070730, 373.457776303265, -373.457411394700, 124.485682162165 },
			.b_size = 4,
			.a = { 1.0, -2.99977292534365, 2.99954585112795, -0.999772925784302 },
			.a_size = 4,
			.sample_time = 0.000001
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
