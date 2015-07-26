#include <dsverifier.h>

digital_system ds = {
        .a = { 1.0000, 9.1122, -2.2473, -8.6564, 0.6569, 0.1355 },
        .a_size = 6,
	.b = { 0.0937, -0.3582, 0.5201, -0.3482, 0.1003, -0.0078 },
	.b_size = 6
};

implementation impl = {
        .int_bits = 2,
        .frac_bits = 13,
};
