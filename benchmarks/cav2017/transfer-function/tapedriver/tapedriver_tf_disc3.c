#include <dsverifier.h>

digital_system controller = { 
	.b = {  0 , 0 , 0 , 0 },
	.b_size =  4,
	.a = {  0 , 0 , 0 , 0 },
	.a_size =  4,
	.sample_time = 5.000000e-01
};

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.02 , -2.7678e-89 , 1.9719e-306 },
	.b_size =  4,
	.a = {  1 , 4.8229e-83 , 9.2917e-166 , 0 },
	.a_size =  4 
	};

