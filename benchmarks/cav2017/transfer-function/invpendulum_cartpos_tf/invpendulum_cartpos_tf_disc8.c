#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 3.126e-11 , 3.1248e-11 , -3.1283e-11 , -3.1271e-11 },
	.b_size =  5,
	.a = {  1 , -4 , 6 , -4 , 1 },
	.a_size =  5 
	};

