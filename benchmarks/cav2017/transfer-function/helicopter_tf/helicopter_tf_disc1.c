#include <dsverifier.h>

digital_system controller = { 
	.b = {  0 , 0 , 0 , 0 },
	.b_size =  4,
	.a = {  0 , 0 , 0 , 0 },
	.a_size =  4,
	.sample_time = 1
};

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 10.7281 , 22.0305 , 17.6877 },
	.b_size =  4,
	.a = {  1 , -2.6207 , 2.3586 , -0.65705 },
	.a_size =  4 
	};

