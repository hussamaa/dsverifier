#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.0024039 , 0.0048078 , 0.0024039 },
	.b_size =  4,
	.a = {  1 , -2.4094 , 2.0129 , -0.60351 },
	.a_size =  4 
	};

