#include <dsverifier.h>

digital_system controller = { 
	.b = {  -111.9575 , 335.5443 , -335.2166 , 111.6298 },
	.b_uncertainty = {  0.015 , 0.015 , 0.015 , 0.015 },
	.b_size =  4,
	.a = {  1 , -2.7957 , 2.5918 , -0.79608 },
	.a_uncertainty = {  0.015 , 0.015 , 0.015 , 0.015 },
	.a_size =  4,
	.sample_time = 1.000000e-03
};

implementation impl = { 
	.int_bits =  9,
	.frac_bits =   7,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0.00049963 , -4.9988e-07 , -0.00050013 },
	.b_uncertainty = {  0.015 , 0.015 , 0.015 },
	.b_size =  3,
	.a = {  1 , -1.9995 , 0.9995 },
	.a_size =  3 
	.a_uncertainty = {  0.015 , 0.015 , 0.015 },
	};

