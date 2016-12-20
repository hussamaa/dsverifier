#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.031315 , 0.031315 },
	.b_size =  3,
	.a = {  1 , -2.0251 , 1 },
	.a_size =  3 
	};

