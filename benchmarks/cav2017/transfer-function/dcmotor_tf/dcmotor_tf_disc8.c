#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 2.3771e-05 , 4.7542e-05 , 2.3771e-05 },
	.b_size =  4,
	.a = {  1 , -2.8943 , 2.7983 , -0.90393 },
	.a_size =  4 
	};

