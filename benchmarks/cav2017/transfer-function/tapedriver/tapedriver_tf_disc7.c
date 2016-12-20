#include <dsverifier.h>

digital_system controller = { 
	.b = {  0 , 0 , 0 , 0 },
	.b_size =  4,
	.a = {  0 , 0 , 0 , 0 },
	.a_size =  4,
	.sample_time = 1.000000e-02
};

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.021294 , -0.00039098 , 1.7706e-08 },
	.b_size =  4,
	.a = {  1 , 0.044641 , 0.00049842 , -2.272e-08 },
	.a_size =  4 
	};

