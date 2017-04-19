#include <dsverifier.h>

digital_system controller = { 
	.b = {  -124.5 , -364.95 , -360.45 , -120 },
	.b_uncertainty = {  0.015 , 0.015 , 0.015 , 0.015 },
	.b_size =  4,
	.a = {  1 , 227.1 , 440.7 , 220 },
	.a_uncertainty = {  0.015 , 0.015 , 0.015 , 0.015 },
	.a_size =  4,
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
	.b_uncertainty = {  0.015 , 0.015 , 0.015 },
	.b_size =  3,
	.a = {  1 , 0.5 , -0.5 },
	.a_size =  3 
	.a_uncertainty = {  0.015 , 0.015 , 0.015 },
	};

