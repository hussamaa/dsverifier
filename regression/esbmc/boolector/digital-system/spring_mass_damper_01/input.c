#include <dsverifier.h>

digital_system ds = {
   .b = {1.280000E3, -1.354240E3, 0.074879E3},    /* digital control numerator coefficients */
   .b_size = 3,                       /* number of coefficients in numerator */   
   .a = {1.0000, -1.4990, 0.4995},            /* digital control denominator coefficients */
   .a_size = 3                        /* number of coefficients in denominator */   
};

implementation impl = {
	.int_bits = 4,
	.frac_bits = 12,
	.max = 1.0,
	.min = -1.0,
};
