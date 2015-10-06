#include "../../../../bmc/dsverifier.h"

#define SCHEMA_COUNT 7

#if SCHEMA_ID == 1

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.300000000000000, -0.200000000000000, -0.500000000000000 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -3.60000000000000, 1.80000000000000 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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

#if SCHEMA_ID == 2

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.0502645502645500, -0.00529100529100530, -0.0555555555555556 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -2.12698412698413, 1.10582010582011 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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
			.b = { 0.0250320924261870, -0.00128369704749679, -0.0263157894736842 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -2.05648267008986, 1.05134788189987 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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

#if SCHEMA_ID == 4

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.0150068559240262, -0.000457061601746992, -0.0154639175257732 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -2.03229901985679, 1.03047077344980 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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
			.b = { 0.00500025126890799, -5.02537815970654e-05, -0.00505050505050505 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -2.01025177144580, 1.01005075631941 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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
			.b = { 0.00250003132871339, -1.25314853569596e-05, -0.00251256281407035 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -2.00506272008421, 1.00501259414278 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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

#if SCHEMA_ID == 7

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.000500000250125188, -5.00250375312809e-07, -0.000500500500500500 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -2.00100250175213, 1.00100050075063 },
			.a_uncertainty = { 0.1, 0.1, 0.1 },
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

#if SCHEMA_ID == 8

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 5.00000000025000e-06, -5.00002500039585e-11, -5.00005000050001e-06 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -2.00001000025000, 1.00001000005000 }, 
			.a_uncertainty = { 0.1, 0.1, 0.1 },
			.a_size = 3,
			.sample_time = 0.00001
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 11.4502063947756, -11.4500939644139 },
			.b_size = 4,
			.a = { 1.0, -1.00007035781332 },
			.a_size = 4,
			.sample_time = 0.00001
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

#if SCHEMA_ID == 9

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 5.00000000000250e-07, -5.00000249981342e-13, -5.00000500000500e-07 },
			.b_uncertainty = { 0.1, 0.1, 0.1 },
			.b_size = 3,
			.a = { 1.0, -2.00000100000250, 1.00000100000050 }, 
			.a_uncertainty = { 0.1, 0.1, 0.1 },
			.a_size = 3,
			.sample_time = 0.000001
		};

	#endif

	#define CONTROL_COUNT 1

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 11.4502063947756, -11.4500939644139 },
			.b_size = 4,
			.a = { 1.0, -1.00007035781332 },
			.a_size = 4,
			.sample_time = 0.000001
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
