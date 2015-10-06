#include "../../../../bmc/dsverifier.h"

#define SCHEMA_COUNT 8

#if SCHEMA_ID == 1

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.171428571428571, -0.114285714285714, -0.285714285714286 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -1.88571428571429, 0.771428571428572 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
			.a_size = 3,
			.sample_time = 0.5
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -2.70561932258292, 4.91891416097458, -2.98975424265897, 0.607457221322442 },
			.b_size = 4,
			.a = { 1.0, -0.246954439828182, -0.800014083515246, 0.356805858742342 },
			.a_size = 4,
			.sample_time = 0.5
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
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
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -1.95604395604396, 0.951159951159951 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
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
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -1.97653596789132, 0.975301018832973 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
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
			.b = { 0.0146666501222221, -0.000446700003722501, -0.0151133501259446 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -1.98555669987964, 0.985109999875917 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
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
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -1.99506228257210, 0.995012406638487 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
			.a_size = 3,
			.sample_time = 0.01
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -10.6541798765226, 28.9820624061405, -26.2822459536125, 7.94546415262250 },
			.b_size = 4,
			.a = { 1.0, -0.976750653540241, -0.695199955503643, 0.688265939892838 },
			.a_size = 4,
			.sample_time = 0.01
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.scale = 1
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 6

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.00249064447766691, -1.24844334720149e-05, -0.00250312891113892 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -1.99751559773907, 0.997503113305597 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
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
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -1.99950062478138, 0.999500124906289 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.scale = 1
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 8

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.000199940009997800, -7.99920023995825e-08, -0.000200020002000200 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -1.99980009998600, 0.999800019994001 }, 
			.a_uncertainty = { 0.1, 0.1, 0.1 },
			.a_size = 3,
			.sample_time = 0.0004
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -119.158714850888, 357.336454078930, -357.196818781631, 119.019079546242 },
			.b_size = 4,
			.a = { 1.0, -2.91304070183424, 2.82614887122274, -0.913108155920450 },
			.a_size = 4,
			.sample_time = 0.0004
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 4,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 2
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 8,
				.scale = 1
			};
		#endif

		#if IMPLEMENTATION_ID == 3
skip
			implementation impl = { 
				.int_bits = 16,
				.frac_bits = 12,
				.scale = 1
			};
		#endif

	#endif

#endif
