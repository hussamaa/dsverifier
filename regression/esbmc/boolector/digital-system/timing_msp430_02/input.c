#include <dsverifier.h>

digital_system ds = {
        .a = { 1.0, 1.0, 0.31, 0.03 },       
        .a_size = 4,
        .b = { 1.0, 6.0, 1.0, 6.0 },
        .b_size = 4,
	.sample_time = 0.00002
};

implementation impl = {
        .int_bits = 15,
        .frac_bits = 16,
        .delta = 0.25,
        .max = 1.0,
        .min = -1.0,
        .scale = 1e6
};

hardware hw = {	
	.clock = 16000000,
	.device = MSP430,
};
