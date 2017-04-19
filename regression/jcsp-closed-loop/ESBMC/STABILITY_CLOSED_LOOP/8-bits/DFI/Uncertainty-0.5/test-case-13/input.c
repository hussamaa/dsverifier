#include <dsverifier.h>

digital_system controller = { 
	.b = {  379 , 39383 , 192306 , 382993 , 383284 , 192175 , 38582 },
	.b_uncertainty = {  0.005 , 0.005 , 0.005 , 0.005 , 0.005 , 0.005 , 0.005 },
	.b_size =  7,
	.a = {  3 , -328 , -38048 , -179760 , -314330 , -239911 , -67626 },
	.a_uncertainty = {  0.005 , 0.005 , 0.005 , 0.005 , 0.005 , 0.005 , 0.005 },
	.a_size =  7,
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
	.b_uncertainty = {  0.005 , 0.005 , 0.005 },
	.b_size =  3,
	.a = {  1 , -1 , -2 },
	.a_size =  3 
	.a_uncertainty = {  0.005 , 0.005 , 0.005 },
	};

