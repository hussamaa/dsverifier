#include <stdlib.h>
#include "../../../../core/util.h"
#include "../../../../core/delta-operator.h"

int main(){
   double a[3] = { 1.0, -1.9, 0.9025 };
   double out[3];
   generate_delta_coefficients(a, out, 3, 0.1);
   printf("%.10f - %.10f - %.10f\n", out[0], out[1], out[2]);	   
   assert(0);
   return 0;
}
