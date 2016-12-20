#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 28.0878 , 67.2432 , 59.4618 },
	.b_size =  4,
	.a = {  1 , -2.4099 , 2.1907 , -0.53259 },
	.a_size =  4 
	};

