#include <dsverifier.h>

digital_system ds = {
   .a = { 1.0f, -0.960f },
   .a_size = 2,
   .b = { 1.5840f, -1.553f },
   .b_size = 2,
};

implementation impl = {
   .int_bits = 3,
   .frac_bits = 5,
   .min = -3.0,
   .max = 3.0
};
