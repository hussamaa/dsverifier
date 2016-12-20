#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.0018609 , 0.0015597 , -0.0024632 , -0.002162 },
	.b_size =  5,
	.a = {  1 , -4.0401 , 6.0803 , -4.0401 , 1 },
	.a_size =  5 
	};

