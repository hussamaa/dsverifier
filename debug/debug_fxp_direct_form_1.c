#include <assert.h>

void __DSVERIFIER_assert(_Bool expression){
	assert(expression);
}

void __DSVERIFIER_assume(_Bool expression){
	/* nothing to do here */
}

#include "../bmc/core/definitions.h"
#include "../bmc/core/fixed-point.h"
#include "../bmc/core/realizations.h"
#include "../bmc/core/util.h"
#include "../bmc/core/functions.h"
#include "../bmc/core/initialization.h"

/*
digital_system ds = {
	.b = { 0.00156250000000000008673617379884, 0.00113125000000000378030939884866, -0.00002499999999998336885909111516, -0.00006999999999998673949619387713 },
	.b_size = 4,
	.a = { 0.01562500000000000000000000000000, 0.02662500000000000976996261670138, 0.00825000000000009059419880941277, 0.00020000000000020001778011646820 },
	.a_size = 4,
	.sample_time = 0.01
};
*/

digital_system ds = {
	.b = { 0.00156250000000000008673617379884, 0.00113125000000000378030939884866, -0.00002499999999998336885909111516, -0.00006999999999998673949619387713 },
	.b_size = 4,
	.a = { 0.01562500000000000000000000000000, 0.02662500000000000976996261670138, 0.00825000000000009059419880941277, 0.00020000000000020001778011646820 },
	.a_size = 4,
	.sample_time = 0.01
};

implementation impl = {
	.int_bits = 3,
	.frac_bits = 16,
	.delta = 0.25,
	.min = -4.0,
	.max = 4.0
};

/*
digital_system ds = { 
        .b = { 0.012500000000000, 0.004525000000000, -0.000050000000000,  -0.000070000000000 },
        .b_size = 4,
        .a = { 0.125000000000000, 0.106500000000000, 0.016500000000000,  0.000200000000000 },
        .a_size = 4,
        .sample_time = 0.02
};
*/
/*
digital_system ds = {
	.b = { 0.100000000000000,   0.036200000000000,  -0.000400000000000,  -0.000560000000000 },
	.b_size = 4,
	.a = { 1.000000000000000,   0.852000000000000,   0.132000000000001,   0.001600000000002 },
	.a_size = 4,
	.sample_time = 0.02
};
*/
/*
implementation impl = {
	.int_bits = 15,
	.frac_bits = 16,
	.delta = 0.25,
	.min = -1.0,
	.max = 1.0
};
*/

hardware hw = { };

/* inputs */
fxp32_t x_fxp[7] = { -262144, 262144, -262144, 262144, -262144, -262144, -262144 };
int x_size = 7;
int generic_timer;

/** fixed point direct form 1 realization (implementation 2) */
void fxp_direct_form_1_impl2_debug(fxp32_t x[], int x_size, fxp32_t b[], int b_size, fxp32_t a[], int a_size, fxp32_t y[]){
   int i = 0; int j = 0;
   /* system 1 h1(z) */
   fxp32_t v[x_size];
   for(i = 0; i < x_size; i++){
      v[i] = 0;
      for(j = 0; j < b_size; j++){
         if (j > i) break;
         v[i] = fxp_add(v[i], fxp_mult(x[i-j], b[j]));
      }
   }

   /* system 2 h2(z) */
   y[0] = v[0];
   /* input here the counterexample values */
   for(i = 1; i < x_size; i++){
	   y[i] = 0;
	   y[i] = fxp_add(y[i], v[i]);
	   for(j = 1; j < a_size; j++){
		   if (j > i) break;
		   y[i] = fxp_add(y[i], fxp_mult(y[i-j] , -a[j]));
	   }
   }
}

int main(){
	
	initialization();

	DSVERIFIER_OVERFLOW_MODE = 1;

	double x[6]; // = { -0.99218750, -0.99218750, -0.99218750, -0.99218750, -0.99218750, -0.99218750, -0.99218750, 1.0, -0.99218750, -0.99218750 } ;
	printf("inputs: \n");
	print_fxp_array_elements("x_fxp", x_fxp, x_size);
	fxp_to_double_array(x, x_fxp, x_size);
	print_array_elements("x", x, x_size);

	printf("\noriginal coefficients: \n");
	print_array_elements("ds.b", ds.b, ds.b_size);
	print_array_elements("ds.a", ds.a, ds.a_size);

	fxp32_t b_fxp[ds.b_size];
	fxp32_t a_fxp[ds.a_size];

	fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);
	fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);

	printf("\nfxp representation: \n");
	print_fxp_array_elements("b_fxp" , b_fxp, ds.b_size);
	print_fxp_array_elements("a_fxp" , a_fxp, ds.a_size);

	double db_fxp[ds.b_size];
	double da_fxp[ds.a_size];

	fxp_to_double_array(db_fxp, b_fxp, ds.b_size);
	fxp_to_double_array(da_fxp, a_fxp, ds.a_size);

	printf("\nquantized coefficients: \n");
	print_array_elements("ds.b_fxp", db_fxp, ds.b_size);
	print_array_elements("ds.a_fxp", da_fxp, ds.a_size);

	/* update with values found in bmc machine */
	fxp32_t xaux[ds.b_size];
	fxp32_t yaux[ds.a_size];
	fxp32_t y0[ds.a_size];
	yaux[0] = 0;
	yaux[1] = 0;
	yaux[2] = 0;
	yaux[3] = 0;

	int i, j;
	/* prepare outputs */
	double y[x_size];
	fxp32_t y_fxp[x_size];
	for (i = 0; i < x_size; i++) {
		y_fxp[i] = 0;
		y[i] = 0;
	}

	for (i = 0; i < ds.b_size; ++i) {
		xaux[i] = 0;
	}

	fxp32_t xk;
	fxp32_t *aptr, *bptr, *xptr, *yptr, *wptr;
	int count = 0;
	int notzeros = 0;

/*	fxp_direct_form_1_impl2_debug(x_fxp, x_size, b_fxp, ds.b_size, a_fxp, ds.a_size, y_fxp); */

	for (i = 0; i < x_size; ++i) {

		shiftL(x_fxp[i], xaux, ds.b_size);
		y_fxp[i] = fxp_direct_form_1(yaux, xaux, a_fxp, b_fxp, ds.a_size, ds.b_size);
		#ifdef JACKSON_RULE
			fxp_quant(y_fxp[i]);
		#endif
		shiftL(y[i], yaux, ds.a_size);
	}

	printf("\noutputs: \n");
	print_fxp_array_elements("y_fxp", y_fxp, x_size);
	fxp_to_double_array(y, y_fxp, x_size);
	print_array_elements("y", y, x_size);

}
