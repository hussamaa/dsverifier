#include <dsverifier.h>

digital_system controller = { 
	.b = {  0 , 0 , 0 , 0 , 0 },
	.b_size =  5,
	.a = {  0 , 0 , 0 , 0 , 0 },
	.a_size =  5,
	.sample_time = 5.000000e-02
};

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 3.069e-05 , 2.9517e-05 , -3.3035e-05 , -3.1862e-05 },
	.b_size =  5,
	.a = {  1 , -4.0025 , 6.005 , -4.0025 , 1 },
	.a_size =  5 
	};

