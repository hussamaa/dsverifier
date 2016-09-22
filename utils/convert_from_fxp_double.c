#include <stdio.h>

int main(){

 int int_bits=4;
 int frac_bits=10;

  int _fxp_min = -(1 << (frac_bits + int_bits) - 1);
  int _fxp_max = ((1 << (frac_bits + int_bits) - 1) - 1);
  double _dbl_min = _fxp_min;
  _dbl_min /= (1 << frac_bits);
  double _dbl_max = _fxp_max;
  _dbl_max /= (1 << frac_bits);

 printf("_dbl_min: %f\n", _dbl_min);
 printf("_dbl_max: %f\n", _dbl_max);
 
 return 0;
}
