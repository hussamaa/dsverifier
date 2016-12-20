#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.13185 , 0.26369 , 0.13185 },
	.b_size =  4,
	.a = {  1 , -0.94241 , -0.051181 , -0.0064093 },
	.a_size =  4 
	};

