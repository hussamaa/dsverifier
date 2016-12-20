#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 2.5016e-10 , 2.4997e-10 , -2.5053e-10 , -2.5034e-10 },
	.b_size =  5,
	.a = {  1 , -4 , 6 , -4 , 1 },
	.a_size =  5 
	};

