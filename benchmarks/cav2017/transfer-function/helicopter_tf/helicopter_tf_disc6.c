#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.47948 , -0.96347 , 0.49162 },
	.b_size =  4,
	.a = {  1 , -2.9792 , 2.9585 , -0.97922 },
	.a_size =  4 
	};

