#include <dsverifier.h>

implementation impl = { 
	.int_bits =  7,
	.frac_bits =   3,
	.max =  1.000000,
	.min =  -1.000000
	};

digital_system plant = { 
	.b = {  0 , 0.02 , -8.4967e-20 , 3.1608e-63 },
	.b_size =  4,
	.a = {  1 , -5.5197e-17 , 9.8542e-34 , -3.6658e-77 },
	.a_size =  4 
	};

