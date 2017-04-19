#include <dsverifier.h>

digital_system controller = { 
	.b = {  11.4497 , 11.2426 },
	.b_uncertainty = {  0.05 , 0.05 },
	.b_size =  2,
	.a = {  1 , -7.0355 },
	.a_uncertainty = {  0.05 , 0.05 },
	.a_size =  2,
	.sample_time = 0
};

implementation impl = { 
	.int_bits =  4,
	.frac_bits =   4,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 1 , -1 },
	.b_uncertainty = {  0.05 , 0.05 , 0.05 },
	.b_size =  3,
	.a = {  1 , -1 , -2 },
	.a_size =  3 
	.a_uncertainty = {  0.05 , 0.05 , 0.05 },
	};

