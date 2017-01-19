#include <dsverifier.h>

digital_system controller = { 
	.b = {  0 , 0 , 0 , 0 , 0 },
	.b_size =  5,
	.a = {  0 , 0 , 0 , 0 , 0 },
	.a_size =  5,
	.sample_time = 1.000000e-01
};

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.00024106 , 0.00022229 , -0.00027862 , -0.00025984 },
	.b_size =  5,
	.a = {  1 , -4.01 , 6.02 , -4.01 , 1 },
	.a_size =  5 
	};

