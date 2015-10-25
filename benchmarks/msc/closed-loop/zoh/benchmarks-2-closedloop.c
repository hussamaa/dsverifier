#include "../../../../bmc/dsverifier.h"

#define SCHEMA_COUNT 9

#if SCHEMA_ID == 1

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.548693198268086, -0.886738807003861 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -3.32481248817168, 1.64872127070013 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.5
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -18.7913011069951, 11.3839445828215 },
			.b_size = 2,
			.a = { 1.0, 3.63545078000333 },
			.a_size = 2,
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
			.b = { 0.100342181002722, -0.110876810062963 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -2.12624017619613, 1.10517091807565 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.1
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 18.5304651429392, -16.7960874196180 },
			.b_size = 2,
			.a = { 1.0, -2.08535650257322 },
			.a_size = 2,
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
			.b = { 0.0500422033454653, -0.0526068264456340 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -2.05640034257636, 1.05127109637602 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.05
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 14.2344952240432, -13.5523885821810 },
			.b_size = 2,
			.a = { 1.0, -1.42685562045612 },
			.a_size = 2,
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

#if SCHEMA_ID == 4

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.0300090687252212, -0.0309228417953966 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -2.03228208009387, 1.03045453395352 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.03
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 12.9891735487942, -12.6121006969068 },
			.b_size = 2,
			.a = { 1.0, -1.23596847805225},
			.a_size = 2,
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
			.b = { 0.0100003341716806, -0.0101008375175585 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -2.01025117377592, 1.01005016708417 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.01
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 11.9254708617320, -11.8089453595694 },
			.b_size = 2,
			.a = { 1.0, -1.07292051194339 },
			.a_size = 2,
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
			.b = { 0.00500004171890647, -0.00502510442763112 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -2.00506264627685, 1.00501252085940 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.005
		};

	#endif
	
	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 11.6833505110710, -11.6261308811661 },
			.b_size = 2,
			.a = { 1.0, -1.03580748101003 },
			.a_size = 2,
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
			.b = { 0.00100000033341672, -0.00100100083375018 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -2.00100250116738, 1.00100050016671 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.001
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 11.4958082843740, -11.4845259551093 },
			.b_size = 2,
			.a = { 1.0, -1.00706037056799 },
			.a_size = 2,
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
			.b = { 1.00000000003333e-05, -1.00001000008333e-05 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -2.00001000025000, 1.00001000005000 }, 
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.00001
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 11.4502063947756, -11.4500939644139 },
			.b_size = 2,
			.a = { 1.0, -1.00007035781332 },
			.a_size = 2,
			.sample_time = 0.00001
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

#if SCHEMA_ID == 9

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 1.00000000000033e-06, -1.00000100000083e-06 },
			.b_uncertainty = { 0, 0 },
			.b_size = 2,
			.a = { 1.0, -2.00000100000250, 1.00000100000050 }, 
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.000001
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 11.4502063947756, -11.4500939644139 },
			.b_size = 2,
			.a = { 1.0, -1.00007035781332 },
			.a_size = 2,
			.sample_time = 0.000001
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
