/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Daniel Mello <dani-dmello@hotmail.com>
 *                
 * ------------------------------------------------------------------------
 *
 * Temporary c script to test magnitude verification functions
 *
 * ------------------------------------------------------------------------
 */

#include "engine/verify_magnitude_and_phase.h"
#include "core/filter_functions.h"
#include "engine/fixed-point.h"

//constants
const int xLen = 10;
const int Alen = 3;
const int Blen = 3;


int main()
{

  double A[] = {1.000000000000000,  -0.369527377351242,   0.195815712655833};
  double B[] = {0.391335772501769,  -0.782671545003537,   0.391335772501769};

  int N = 100;
  double res[N+1];
  int i,j;
  double y[xLen]; 

  for (i=0; i<Blen; i++) {
    B[i] = fxp_to_float(fxp_float_to_fxp(B[i]);
    printf("B[%d]=%f \n", i, B[i]);
  }
  for (i=0; i<Alen; i++) {
    A[i] = fxp_to_float(fxp_float_to_fxp(A[i]));
    printf("A[%d]=%f \n", i, A[i]);
  }

  
  resp_mag(B, Blen, A, Alen, *res, N);
   

  struct filter_parameters prop = {
        .Ap =  0.81, .Ac =  0.7, .Ar = 0.5,
        .wp = 0.5, .wc = 0.4, .wr = 0.3, 
    };
  verify_magnitude(prop, res, N);
  return 0;
}