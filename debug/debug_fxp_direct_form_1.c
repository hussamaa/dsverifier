#include <assert.h>

void __DSVERIFIER_assert(_Bool expression){
	assert(expression);
}

void __DSVERIFIER_assume(_Bool expression){
	/* nothing to do here */
}

#include "../core/definitions.h"
#include "../core/fixed-point.h"
#include "../core/realizations.h"
#include "../core/util.h"
#include "../core/functions.h"
#include "../core/initialization.h"

digital_system ds = { 
	.b = { 2002.0, -4000.0, 1998.0 },
	.b_size = 3,
	.a = { 1.0, 0.0, -1.0 },
	.a_size = 3,
	.sample_time = 0.001
};

implementation impl = { 
	.int_bits = 13,
	.frac_bits = 3,
	.max = 1.0,
	.min = -1.0,
};

hardware hw = { };

/* inputs */
fxp32_t x_fxp[20] = { 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8};
int x_size = 20;
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
   y[0] = 8;
   y[1] = 8;
   y[2] = 0;
   /* input here the counterexample values */
   for(i = 3; i < x_size; i++){
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

	OVERFLOW_MODE = 3;

	double x[x_size];
	printf("inputs: \n");
	fxp_to_double_array(x, x_fxp, x_size);
	print_array_elements("x", x, x_size);
	print_fxp_array_elements("x_fxp", x_fxp, x_size);

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

	fxp_direct_form_1_impl2_debug(x_fxp, x_size, b_fxp, ds.b_size, a_fxp, ds.a_size, y_fxp);

	printf("\noutputs: \n");
	print_fxp_array_elements("y_fxp", y_fxp, x_size);
	fxp_to_double_array(y, y_fxp, x_size);
	print_array_elements("y", y, x_size);

}
