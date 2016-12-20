#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 4.4438 , -3.1876 , 5.706 },
	.b_size =  4,
	.a = {  1 , -2.8067 , 2.6285 , -0.81058 },
	.a_size =  4 
	};

