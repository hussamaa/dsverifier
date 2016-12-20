#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.02 , -3.6097e-37 , 4.9955e-124 },
	.b_size =  4,
	.a = {  1 , -1.0758e-33 , 9.7104e-67 , -1.3438e-153 },
	.a_size =  4 
	};

