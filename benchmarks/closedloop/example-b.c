#include <dsverifier.h>

#define SCHEMA_COUNT 8

#if SCHEMA_ID == 1

	#define PLANT_COUNT 1

	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.335275509257994, -0.558786095915934 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -1.89055607640038, 0.778800783071405 },
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
			.a = { 1.0, -0.246954439828182, -0.800014083515246, 0.356805858742342 },
			.a_size = 4,
			.sample_time = 0.5
		};

		#define	IMPLEMENTATION_COUNT 3

		#if IMPLEMENTATION_ID == 1
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 4
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 8
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 12
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 2

	#define PLANT_COUNT 1

	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.0927027117013712, -0.102460891523910 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -1.95610851441198, 0.951229424500714 },
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
				.frac_bits = 4
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 8
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 12
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 3

	#define PLANT_COUNT 1

	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.0481506869827621, -0.0506199529763825 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -1.97654454502514, 0.975309912028333 },
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
				.frac_bits = 4
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 8
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 12
			};
		#endif

	#endif

#endif

//

#if SCHEMA_ID == 4

	#define PLANT_COUNT 1

	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.0293305788581764, -0.0302238959805054 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -1.98555859816423, 0.985111939603063 },
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
				.frac_bits = 4
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 8
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 12
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 5

	#define PLANT_COUNT 1

	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.00992520776150855, -0.0100249585932822 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -1.99506235460857, 0.995012479192682 },
			.a_uncertainty = { 0, 0, 0 },
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
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 4
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 8
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 12
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 6

	#define PLANT_COUNT 1

	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.00498127600589352, -0.00500624480792807 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -1.99751560679848, 0.997503122397460 },
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
				.frac_bits = 4
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 8
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 12
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 7

	#define PLANT_COUNT 1

	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.000999250208276053, -0.00100024995835937 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -1.99950062485421, 0.999500124979169 },
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
				.frac_bits = 4
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 8
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 12
			};
		#endif

	#endif

#endif

#if SCHEMA_ID == 8

	#define PLANT_COUNT 1

	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.000399880013331867, -0.000400039997334000 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -1.99980009999067, 0.999800019998667 },
			.a_uncertainty = { 0, 0, 0 },
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
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 4
			};
		#endif

		#if IMPLEMENTATION_ID == 2
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 8
			};
		#endif

		#if IMPLEMENTATION_ID == 3
			implementation impl = {
				.int_bits = 16,
				.frac_bits = 12
			};
		#endif

	#endif

#endif
