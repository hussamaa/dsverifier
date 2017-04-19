#include <dsverifier.h>

digital_system controller = { 
	.b = {  11.4958 , -11.4845 },
	.b_uncertainty = {  0.015 , 0.015 },
	.b_size =  2,
	.a = {  1 , -1.0071 },
	.a_uncertainty = {  0.015 , 0.015 },
	.a_size =  2,
	.sample_time = 1.000000e-03
};

implementation impl = { 
	.int_bits =  4,
	.frac_bits =   4,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0.0005 , -5.0025e-07 , -0.0005005 },
	.b_uncertainty = {  0.015 , 0.015 , 0.015 },
	.b_size =  3,
	.a = {  1 , -2.001 , 1.001 },
	.a_size =  3 
	.a_uncertainty = {  0.015 , 0.015 , 0.015 },
	};

