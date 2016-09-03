#include <assert.h>

void __DSVERIFIER_assert(_Bool expression){
	assert(expression);
}

void __DSVERIFIER_assume(_Bool expression){
	/* nothing to do here */
}

#include "../../bmc/core/definitions.h"
#include "../../bmc/core/fixed-point.h"
#include "../../bmc/core/realizations.h"
#include "../../bmc/core/util.h"
#include "../../bmc/core/functions.h"
#include "../../bmc/core/initialization.h"
#include <stdlib.h>
#include <stdio.h>
/*
digital_system ds = {
	.b = { 0.1, -0.2819, 0.2637, -0.08187 },
	.b_size = 4,
	.a = { 1.0, -2.574, 2.181, -0.6068 },
	.a_size = 4,
	.sample_time = 0.01
};
*/

digital_system ds = {
	.b = { 0.0625, -0.3125, 0.25, -0.125 },
	.b_size = 4,
	.a = { 1, -2.625, 2.125, -0.625 },
	.a_size = 4,
	.sample_time = 0.01
};

implementation impl = {
	.int_bits = 3,
	.frac_bits = 4,
	.min = -4.0,
	.max = 4.0
};

hardware hw = { };

/* inputs */
fxp_t x_fxp[6];
int x_size = 6;
int generic_timer;

int main(){

	initialization();

	OVERFLOW_MODE = DETECT_OVERFLOW;
	rounding_mode = FLOOR;

	double x[6] = { 0.625, -0.0625, -4.0, -4.0, -2.4375, 4.0 };
	printf("inputs: \n");
	fxp_double_to_fxp_array(x, x_fxp, x_size);
	print_array_elements("x", x, x_size);
	print_fxp_array_elements("x_fxp", x_fxp, x_size);
	double x_qtz[6];
	fxp_to_double_array(x_qtz, x_fxp, x_size);
	print_array_elements("x_qtz", x, x_size);

	printf("\noriginal coefficients: \n");
	print_array_elements("ds.b", ds.b, ds.b_size);
	print_array_elements("ds.a", ds.a, ds.a_size);

	fxp_t b_fxp[ds.b_size];
	fxp_t a_fxp[ds.a_size];

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
	fxp_t xaux[ds.b_size];
	fxp_t yaux[ds.a_size];
	fxp_t y0[ds.a_size];
	yaux[0] = 0;
	yaux[1] = 0;
	yaux[2] = 0;
	yaux[3] = 0;

	int i, j;
	/* prepare outputs */
	double y[x_size];
	fxp_t y_fxp[x_size];
	for (i = 0; i < x_size; i++) {
		y_fxp[i] = 0;
		y[i] = 0;
	}

	for (i = 0; i < ds.b_size; ++i) {
		xaux[i] = 0;
	}

	fxp_t xk;
	fxp_t *aptr, *bptr, *xptr, *yptr, *wptr;
	int count = 0;
	int notzeros = 0;

	for (i = 0; i < x_size; ++i) {
		shiftL(x_fxp[i], xaux, ds.b_size);
		y_fxp[i] = fxp_direct_form_1(yaux, xaux, a_fxp, b_fxp, ds.a_size, ds.b_size);
		shiftL(y_fxp[i], yaux, ds.a_size);
	}

	printf("\noutputs: \n");
	print_fxp_array_elements("y_fxp", y_fxp, x_size);
	fxp_to_double_array(y, y_fxp, x_size);
	print_array_elements("y", y, x_size);

	fxp_verify_overflow_array(y_fxp, x_size);	

	double xn=-3.375;
	fxp_t xf = fxp_double_to_fxp(xn);
	fxp_t yn2 = -23;
	//fxp_t yn2 = 276;
	//fxp_t yn1 = -260;
	fxp_t yn1 = -3;

	fxp_t y_current = fxp_sub(fxp_sub(fxp_add(fxp_add(fxp_mult(b_fxp[0],xf),fxp_mult(b_fxp[1], xf)),fxp_mult(b_fxp[2],xf)),fxp_mult(a_fxp[1],yn1)),fxp_mult(a_fxp[2],yn2));

	printf("y = %d\n", y_current);

}
