#include <dsverifier.h>

digital_system controller = { 
	.b = {  141.0736 , -832.4397 , 2046.163 , -2681.7266 , 1976.4949 , -776.7051 , 127.1399 },
	.b_uncertainty = {  0.005 , 0.005 , 0.005 , 0.005 , 0.005 , 0.005 , 0.005 },
	.b_size =  7,
	.a = {  1 , -6.1296 , 15.6342 , -21.2414 , 16.2144 , -6.5937 , 1.1161 },
	.a_uncertainty = {  0.005 , 0.005 , 0.005 , 0.005 , 0.005 , 0.005 , 0.005 },
	.a_size =  7,
	.sample_time = 1.000000e-03
};

implementation impl = { 
	.int_bits =  29,
	.frac_bits =   2,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0.0005 , -5.0025e-07 , -0.0005005 },
	.b_uncertainty = {  0.005 , 0.005 , 0.005 },
	.b_size =  3,
	.a = {  1 , -2.001 , 1.001 },
	.a_size =  3 
	.a_uncertainty = {  0.005 , 0.005 , 0.005 },
	};

