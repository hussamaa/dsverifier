#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.02 , -4.1223e-11 , 7.9509e-33 },
	.b_size =  4,
	.a = {  1 , 1.0862e-08 , 3.1391e-17 , -6.0546e-39 },
	.a_size =  4 
	};

