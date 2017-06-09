#include <dsverifier.h>

#if DS_ID == 1

digital_system ds = {
        .b = {  0.00390625, 0.0009765625 },
        .b_size = 2,
        .a = { 0.3134765625, -0.0009765625 },
        .a_size = 2,
        .sample_time = 0.2
};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 
implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0
};

	#endif 

#endif

#if DS_ID == 2

digital_system ds = {
        .b = { -0.3466796875, 0.015625 },
        .b_size = 2,
        .a = { 0.5, 0.19921875, 0.0 },
        .a_size = 3,
        .sample_time = 2
};
	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 
implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0
};

	#endif 

#endif

#if DS_ID == 3

digital_system ds = {
        .b = { 0.5, -0.96875, -0.875, -0.5},
        .b_size = 4,
        .a = { 0.001190185546875, 0.0008544921875, 0.000152587890625, 0.000335693359375, 0, 0, 0, 0, 0 },
        .a_size = 9,
        .sample_time = 0.01
};
	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 
implementation impl = {
        .int_bits = 4,
        .frac_bits = 11,
        .max = 1.0,
        .min = -1.0
};

	#endif 

#endif

#if DS_ID == 4

digital_system ds = {
        .b = { -0.580535888671875, 0.919769287109375, 0.11871337890625, -0.951934814453125 },
        .b_size = 4,
        .a = { 0.7188720703125, -0.38751220703125, -0.415924072265625, 0.437286376953125},
        .a_size = 4,
        .sample_time = 0.01
};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 
implementation impl = {
        .int_bits = 4,
        .frac_bits = 11,
        .max = 1.0,
        .min = -1.0
};

	#endif 

#endif

#if DS_ID == 5

digital_system ds = { 
	.b = {  0,-0.00097656,0,0 },
	.b_size =  4,
	.a = {  0.76172,0,0,0 },
	.a_size =  4,
	.sample_time = 2
};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 
implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0
};

	#endif 

#endif

#if DS_ID == 6

digital_system ds = { 
	.b = {  0,-0.96484,0.9834 },
	.b_size =  3,
	.a = {  0.88965,-0.875,0 },
	.a_size =  3,
	.sample_time = 2
};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 
implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0
};

	#endif 

#endif

#if DS_ID == 7

digital_system ds = { 
	.b = {  0,0.83594,0.26562,-0.96875 },
	.b_size =  4,
	.a = {  0.94531,0.90625,-0.15625,-0.12305 },
	.a_size =  4,
	.sample_time = 0.001
};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 
implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0
};

	#endif 

#endif

#if DS_ID == 8

digital_system ds = { 
	.b = {  -4.6566e-10,1,-1 },
	.b_size =  3,
	.a = {  1,-4.6566e-10,4.6566e-10 },
	.a_size =  3,
	.sample_time = 0.001
};

	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 
implementation impl = {
        .int_bits = 15,
        .frac_bits = 16,
        .max = 1.0,
        .min = -1.0
};

	#endif 

#endif

#if DS_ID == 9

digital_system ds = {
        .b = { -0.0224609375, 0, 0, 0  },
        .b_size = 4,
        .a = { 0.138671875, 0, 0, 0, 0 },
        .a_size = 5,
        .sample_time = 2
};
	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 
implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0
};

	#endif 

#endif

#if DS_ID == 10

digital_system ds = {
        .b = { 0, 0.0625 },
        .b_size = 2,
        .a = { 0.517578125, -0.4990234375 },
        .a_size = 2,
        .sample_time = 2,
};
	#define	IMPLEMENTATION_COUNT 1

	#if IMPLEMENTATION_ID == 1 
implementation impl = {
        .int_bits = 3,
        .frac_bits = 7,
        .max = 1.0,
        .min = -1.0
};

	#endif 

#endif
