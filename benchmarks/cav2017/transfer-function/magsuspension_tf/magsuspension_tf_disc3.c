#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 9198321.5059 , 9198321.4979 },
	.b_size =  3,
	.a = {  1 , -7358659.2048 , 0.99373 },
	.a_size =  3 
	};

