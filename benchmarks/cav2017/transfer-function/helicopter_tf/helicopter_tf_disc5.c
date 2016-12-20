#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.94085 , -1.8695 , 0.98909 },
	.b_size =  4,
	.a = {  1 , -2.9589 , 2.9179 , -0.95887 },
	.a_size =  4 
	};

