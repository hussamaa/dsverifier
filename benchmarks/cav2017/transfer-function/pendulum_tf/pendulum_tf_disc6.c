#include <dsverifier.h>

digital_system controller = { 
	.b = {  0 , 0 , 0 },
	.b_size =  3,
	.a = {  0 , 0 , 0 },
	.a_size =  3,
	.sample_time = 5.000000e-02
};

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.0012474 , 0.0012474 },
	.b_size =  3,
	.a = {  1 , -1.9755 , 1 },
	.a_size =  3 
	};

