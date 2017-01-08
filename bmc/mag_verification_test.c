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
#define LOW_PASS 1
#define HIGH_PASS 2


typedef struct {
   int int_bits;
   int frac_bits;
   double max;
   double min;
   int default_realization;
   double delta;
   int scale;
   double max_error;
} implementation;


typedef struct{

  float Ap, Ar, Ac;
  float wp, wc, wr; 
  int type; 

}filter_parameters;

typedef struct {
  double a[100];
  int a_size;
  double b[100];
  int b_size;
} digital_system;



filter_parameters prop;
implementation impl;
digital_system ds;

#include <math.h>
#include "engine/verify_magnitude_and_phase.h"
//#include "core/filter_functions.h"

//lp2
#define PASS_ID LOW_PASS
#define IMPLEMENTATION_ID 1
#define DS_ID 1
#define CUTTOF_FREQ 9600

#include <math.h>
#include "Filters.h"

//#include "engine/fixed-point.h"

typedef int64_t fxp_t;

/*
//constants
const int xLen = 10;
const int Alen = 3;
const int Blen = 3;
*/


/** scale factor for fixed-point - float conversion */
static const double scale_factor[31] = { 1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0,
    128.0, 256.0, 512.0, 1024.0, 2048.0, 4096.0, 8192.0, 16384.0, 32768.0,
    65536.0, 131072.0, 262144.0, 524288.0, 1048576.0, 2097152.0, 4194304.0,
    8388608.0, 16777216.0, 33554432.0, 67108864.0, 134217728.0,
    268435456.0, 536870912.0, 1073741824.0 };

/** scale factor for fixed-point - float conversion (reciprocal) */
static const double scale_factor_inv[31] = { 1.0, 0.5, 0.25, 0.125, 0.0625,
    0.03125, 0.015625, 0.0078125, 0.00390625, 0.001953125, 0.0009765625,
    0.00048828125, 0.000244140625, 0.0001220703125, 0.00006103515625,
    0.000030517578125, 0.000015258789063, 0.000007629394531,
    0.000003814697266, 0.000001907348633, 0.000000953674316,
    0.000000476837158, 0.000000238418579, 0.000000119209290,
    0.000000059604645, 0.000000029802322, 0.000000014901161,
    0.000000007450581, 0.000000003725290, 0.000000001862645,
    0.000000000931323 };




fxp_t fxp_float_to_fxp(float f) {
  fxp_t tmp;
  double ftemp;
  ftemp = f * scale_factor[impl.frac_bits];
  if(f >= 0) {
    tmp = (fxp_t)(ftemp + 0.5);
  }
  else {
    tmp = (fxp_t)(ftemp - 0.5);
  }
  return tmp;
}

float fxp_to_float(fxp_t fxp) {
  float f;
  int f_int = (int) fxp;
  f = f_int * scale_factor_inv[impl.frac_bits];
  return f;
}



fxp_t fxp_double_to_fxp(double value) {
  fxp_t tmp;
  double ftemp = value * scale_factor[impl.frac_bits];

    if(value >= 0) {
      tmp = (fxp_t)(ftemp + 0.5);
    }
    else {
      tmp = (fxp_t)(ftemp - 0.5);
    }

  return tmp;
}


double fxp_to_double(fxp_t fxp) {
  double f;
  int f_int = (int) fxp;
  f = f_int * scale_factor_inv[impl.frac_bits];
  return f;
}




int main()
{

  //choose_filter(LOW_PASS, 1, 1);
  //choose_filter(HIGH_PASS, 1, 1);
  //choose_filter(LOW_PASS, 2, 3);
  //choose_filter(LOW_PASS, 2, 7);


  //hp2
  /*
  double A[] = {1.000000000000000,  -0.369527377351242,   0.195815712655833};
  double B[] = {0.391335772501769,  -0.782671545003537,   0.391335772501769};
  */
  /*
  //lp2
  double A[] = {1                , -0.369527377351241, 0.195815712655833}; //Den
  double B[] = {0.206572083826148,  0.413144167652296, 0.206572083826148}; //Num
*/

  //lp2EST
  
//  double A[] = { 1.000000000000000, -1.981488509144574, 9.816582826171342e-01}; //Den
// double B[] = {4.244336814021699e-05, 8.488673628043397e-05, 4.244336814021699e-05}; //Num




  int N = 100;
  double res[N+1];
  int i,j;
 // double y[xLen]; 

  for (i=0; i<ds.b_size; i++) {
    ds.b[i] = fxp_to_double(fxp_double_to_fxp(ds.b[i]));
    printf("B[%d]=%.20f \n", i, ds.b[i]);
  }
  for (i=0; i<ds.a_size; i++) {
    ds.a[i] = fxp_to_double(fxp_double_to_fxp(ds.a[i]));
    printf("A[%d]=%.20f \n", i, ds.a[i]);
  }  
  printf("Flag 1\n");
  resp_mag(ds.b, ds.b_size, ds.a, ds.a_size, res, N);
  





  /*LP
  struct filter_parameters prop = {
        .Ap =  0.81, .Ac =  0.7, .Ar = 0.5,
        .wp = 0.5, .wc = 0.4, .wr = 0.3, 
        .type = 2
    };
*/ //hp2

    /*
  struct filter_parameters prop = {
        .Ap =  0.8, .Ac =  0.707945784384138, .Ar = 0.5,
        .wp = 0.3, .wc = 0.4, .wr = 0.5,
        .type =
    };
*/ //lp2

/*
  struct filter_parameters prop = {
        .Ap =  0.8, .Ac =  0.707945784384138, .Ar = 0.5,
        .wp = 0.3, .wc = 0.4, .wr = 0.5,
        .type = 1
    };
    //lp2EST
*/
  verify_magnitude(prop, res, N);

 

  return 0;
}