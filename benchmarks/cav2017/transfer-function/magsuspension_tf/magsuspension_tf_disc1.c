#include <dsverifier.h>

digital_system controller = { 
	.b = {  0 , 0 , 0 },
	.b_size =  3,
	.a = {  0 , 0 , 0 },
	.a_size =  3,
	.sample_time = 1
};

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 67687331614573.01 , 67837515882861.03 },
	.b_size =  3,
	.a = {  1 , -54149865291660.41 , 423045822591.0969 },
	.a_size =  3 
	};

