#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 3.8328 , 3.8328 },
	.b_size =  3,
	.a = {  1 , -5.0662 , 1 },
	.a_size =  3 
	};

