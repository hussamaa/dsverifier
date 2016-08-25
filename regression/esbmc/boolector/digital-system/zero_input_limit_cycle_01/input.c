#include <dsverifier.h>

digital_system ds = {
   .a = { 1.0, 0.0, -0.25 },
   .a_size = 2,
   .b = { 0.2, -0.4, 0.2 },
   .b_size = 2,
};

implementation impl = {
   .int_bits = 3,
   .frac_bits = 12,
   .min = -1.0,
   .max = 1.0
};
