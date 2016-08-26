#include <dsverifier.h>

digital_system ds = {
    .b = { 2.72, -4.153, 1.896 },
    .b_size = 3,
    .a = { 1.0, -1.844, 0.8496},
    .a_size = 3,
    .sample_time = 0.2
};

implementation impl = {
	.int_bits = 4,
	.frac_bits = 12,
	.max = 1.0,
	.min = -1.0,
};
