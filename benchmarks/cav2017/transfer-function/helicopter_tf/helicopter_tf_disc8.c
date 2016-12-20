#include <dsverifier.h>

digital_system controller = { 
	.b = {  0 , 0 , 0 , 0 },
	.b_size =  4,
	.a = {  0 , 0 , 0 , 0 },
	.a_size =  4,
	.sample_time = 5.000000e-03
};

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.048888 , -0.097891 , 0.04901 },
	.b_size =  4,
	.a = {  1 , -2.9979 , 2.9958 , -0.9979 },
	.a_size =  4 
	};

