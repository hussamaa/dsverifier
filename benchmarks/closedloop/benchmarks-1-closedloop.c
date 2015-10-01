#include<dsverifier.h>

#define SCHEMA_COUNT 7

#if SCHEMA_ID == 1

	#define PLANT_COUNT 1
	
	#if PLANT_ID == 1

		digital_system plant = {
			.b = { 0.3, -0.2, -0.5 },
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -3.6, 1.8 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.5
		};

	#endif
	
	#define CONTROL_COUNT 2

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -4.43663402456799, 9.17704235378731,	-3.63624211956520, -5.14442747676007,	5.91666342685494, -2.27907441438503, 0.313287912258803 },
			.b_size = 7,
			.a = { 1.0,	-0.233391114199130,	-1.51948393817180, 0.739991533774660,	0.510291777806688, -0.414030563985704, 0.0732939531502233 },
			.a_size = 7,
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

	#if CONTROL_ID == 2

		digital_system control = { 
			.b = { -18.791300911312852, 11.3839447785038 },
			.b_size = 2,
			.a = { 1.0, 3.635450780003331 },
			.a_size = 2,
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
			.b = { 0.050264550264550, -0.005291005291005, -0.0555555555555556 },
			.b_uncertainty = { 0, 0, 0 },                     
			.b_size = 3,
			.a = { 1.0, -2.126984126984127, 1.105820105820106 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.1
		};

	#endif

	#define CONTROL_COUNT 2

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -21.6434827391792, 83.4927891546905, -112.036459174877, 42.5955412652627,	33.8311612037550, -34.9214748381314, 8.68163510496198 },
			.b_size = 7,
			.a = { 1.0, -1.75602200932015, -0.955448295274541, 3.25220596822767, -1.18043204955751, -0.774291257161577, 0.414495992326059 },
			.a_size = 7,
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

	#if CONTROL_ID == 2

		digital_system control = { 
			.b = { 18.530465097121700, -16.7960874654355 },
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
			.b = { 0.025032092426187, -0.001283697047497, -0.0263157894736842 },
			.b_uncertainty = { 0, 0, 0 },                         
			.b_size = 3,
			.a = { 1.0, -2.056482670089859, 1.051347881899872 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.05
		};

	#endif
		
	#define CONTROL_COUNT 2

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -46.6850612624154, 202.180761312178, 328.057446643219, 222.468419901698, -20.6721114319024, -44.6266276963473, 15.3920469303122 },
			.b_size = 7,
			.a = { 1.0, -1.94601630366264, -1.13797058031406, 4.84519961518936, -3.18005694216105, 0.108927409201867, 0.309949911345490 },
			.a_size = 7,
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

	#if CONTROL_ID == 2

		digital_system control = { 
			.b = { 14.2344952060238, -13.5523886002004 },
			.b_size = 2,
			.a = { 1.0 , -1.42685562045612 },
			.a_size = 2,
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
			.b = { 0.0150068559240260, -0.000457061601746992, -0.0154639175257732 },    
			.b_uncertainty = { 0, 0, 0 },                     
			.b_size = 3,
			.a = { 1.0, -2.03229901985679, 1.03047077344980 },
			.a_uncertainty = { 0, 0, 0 },  
			.a_size = 3,
			.sample_time = 0.03
		};

	#endif

	#define CONTROL_COUNT 2

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { -91.3512094034977, 425.401158225073, -773.764417082585,	667.081991975055, -242.431935896133, -0.223398677743817, 15.2878083267511 },
			.b_size = 7,
			.a = { 1.0, -1.69035849228346, -2.77350585136311, 8.48190524693308, -6.87683627071507, 1.85431102829784, 0.00448877907960656 },
			.a_size = 7,
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

	#if CONTROL_ID == 2

		digital_system control = { 
			.b = { 12.9891735388330, -12.6121007068681 },
			.b_size = 2,
			.a = { 1.0,	-1.23596847805225 },
			.a_size = 2,
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
			.b = { 0.00500025126890799, -5.02537815970654e-05, -0.00505050505050505 },        
			.b_uncertainty = { 0, 0, 0 },                 
			.b_size = 3,
			.a = { 1.0, -2.01025177144580, 1.01005075631941 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.01
		};

	#endif

	#define CONTROL_COUNT 2

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 1504.07003717387, -7953.93417599762,	17259.9261507859, -19580.7517409084,	12160.9995713981, -3874.19781620075, 483.887973848833 },
			.b_size = 7,
			.a = { 1.0, -24.7013361500021, 97.9424782877352, -165.238527671094,	140.065778337054, -58.6792687189003, 9.61087574007062 },
			.a_size = 7,
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

	#if CONTROL_ID == 2

		digital_system control = { 
			.b = { 11.9254708586537, -11.8089453626476 },
			.b_size = 2,
			.a = { 1.0,	-1.07292051194339 },
			.a_size = 2,
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
			.b = { 0.00250003132871339, -1.25314853569596e-05, -0.00251256281407035 }, 
			.b_uncertainty = { 0, 0, 0 },                        
			.b_size = 3,
			.a = { 1.0, -2.00506272008421, 1.00501259414278 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.005
		};

	#endif

	#define CONTROL_COUNT 2

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 246.813760786885, -1376.84994347326, 3184.55948285394, -3905.98877931895,	2676.90258805810, -970.709616619514, 145.272507713111 },
			.b_size = 7,
			.a = { 1.0, -7.34483823558483, 21.2161931801558, -31.4281801129669,	25.4356613467883, -10.7273642855878, 1.84852810665060 },
			.a_size = 7,
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

	#if CONTROL_ID == 2

		digital_system control = { 
			.b = { 11.6833505095594, -11.6261308826777 },
			.b_size = 2,
			.a = { 1.0, -1.03580748101003 },
			.a_size = 2,
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
			.b = { 0.000500000250125188, -5.00250375312809e-07, -0.000500500500500500 },                         
			.b_uncertainty = { 0, 0, 0 },
			.b_size = 3,
			.a = { 1.0, -2.00100250175213, 1.00100050075063 },
			.a_uncertainty = { 0, 0, 0 },
			.a_size = 3,
			.sample_time = 0.001
		};

	#endif

	#define CONTROL_COUNT 2

	#if CONTROL_ID == 1

		digital_system control = { 
			.b = { 127.691976050117, -764.831186975385,	1908.77693888181, -2540.63540664733,	1902.17681565323, -759.551088315499, 126.371951353052 },
			.b_size = 7,
			.a = { 1.0, -6.01112135438694, 15.0554791536785, -20.1107031311171,	15.1104480151390, -6.05509647970606, 1.01099379639260 },
			.a_size = 7,
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

	#if CONTROL_ID == 2

		digital_system control = { 
			.b = { 11.4958082840759, -11.4845259554074 },
			.b_size = 2,
			.a = { 1.0, -1.00706037056799 },
			.a_size = 2,
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
