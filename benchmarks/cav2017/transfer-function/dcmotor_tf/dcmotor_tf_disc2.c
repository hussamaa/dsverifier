#include <dsverifier.h>

digital_system controller = { 
	.b = {  0 , 0 , 0 , 0 },
	.b_size =  4,
	.a = {  0 , 0 , 0 , 0 },
	.a_size =  4,
	.sample_time = 1.500000e+00
};

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.37148 , 0.74296 , 0.37148 },
	.b_size =  4,
	.a = {  1 , -1.0009 , 0.00091661 , -2.6329e-07 },
	.a_size =  4 
	};

