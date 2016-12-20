#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.014486 , 0.028972 , 0.014486 },
	.b_size =  4,
	.a = {  1 , -1.7793 , 1.1436 , -0.36422 },
	.a_size =  4 
	};

