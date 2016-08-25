#include <dsverifier.h>

digital_system ds = {
	.a = { 1.0, 0.0, 0.3 },        
        .a_size = 3,
	.b = { 0.15, 0.05, 0.4 }, 
	.b_size = 3
};

implementation impl = {
        .int_bits = 4,
        .frac_bits = 8,
};
