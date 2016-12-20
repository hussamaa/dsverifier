#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 1.8256 , -3.3694 , 2.0176 },
	.b_size =  4,
	.a = {  1 , -2.9194 , 2.8396 , -0.91943 },
	.a_size =  4 
	};

