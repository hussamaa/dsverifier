#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.062109 , 0.12422 , 0.062109 },
	.b_size =  4,
	.a = {  1 , -0.87892 , 0.011578 , -0.13266 },
	.a_size =  4 
	};

