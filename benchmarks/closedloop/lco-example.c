#include <dsverifier.h>

digital_system plant = {
  .b = { 0.100342181002722, -0.110876810062963 },
  .b_uncertainty = { 0, 0 },
  .b_size = 2,
  .a = { 1.0, -2.12624017619613, 1.10517091807565 },
  .a_uncertainty = { 0, 0, 0 },
  .a_size = 3,
  .sample_time = 0.1
};

digital_system control = {
  .b = { 18.5304651429392, -16.7960874196180 },
  .b_size = 2,
  .a = { 1.0, -2.08535650257322 },
  .a_size = 2,
  .sample_time = 0.1
};

implementation impl = {
  .int_bits = 16,
  .frac_bits = 4
};
