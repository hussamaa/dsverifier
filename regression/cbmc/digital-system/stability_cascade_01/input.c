#include<dsverifier.h>

digital_system ds = {
        .a = { 1.0000, -0.4730, -0.5881, 0.7597, -0.2340, -0.0801, 0.0537, -0.0071 },
        .a_size = 8,
	.b = { 0.0937,-0.3582, 0.5201, -0.3482, 0.1003, -0.0078 },
	.b_size = 6
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 16,
	.delta = 0.25
};

