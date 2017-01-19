#include <dsverifier.h>

digital_system controller = { 
	.b = {  0 , 0 , 0 , 0 , 0 },
	.b_size =  5,
	.a = {  0 , 0 , 0 , 0 , 0 },
	.a_size =  5,
	.sample_time = 1.000000e-02
};

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 2.4919e-07 , 2.4731e-07 , -2.5294e-07 , -2.5107e-07 },
	.b_size =  5,
	.a = {  1 , -4.0001 , 6.0002 , -4.0001 , 1 },
	.a_size =  5 
	};

