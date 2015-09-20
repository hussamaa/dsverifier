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

digital_system ds = { 
	.b = { 0.100000000000000,   0.036200000000000,  -0.000400000000000,  -0.000560000000000 },
	.b_size = 4,
	.a = { 1.000000000000000,   0.852000000000000,   0.132000000000001,   0.001600000000002 },
	.a_size = 4,
	.sample_time = 0.02
};

implementation impl = { 
	.int_bits = 15,
	.frac_bits = 16,
	.max = 1.0,
	.min = -1.0,
};

hardware hw = { };

/* inputs */
fxp32_t x_fxp[20];
int x_size = 20;
int generic_timer;

int main(){
	
	initialization();

	DSVERIFIER_OVERFLOW_MODE = 3;

	double x[10] = { -0.99218750, -0.99218750, -0.99218750, -0.99218750, -0.99218750, -0.99218750, -0.99218750, 1.0, -0.99218750, -0.99218750 } ;
	printf("inputs: \n");
	fxp_double_to_fxp_array(x, x_fxp, x_size);
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

	int Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;

	/* update with values found in bmc machine */
	fxp32_t waux[Nw];
	waux[0] = 0;
	waux[1] = 0;
	waux[2] = 0;
	waux[3] = 0;
	waux[4] = 0;

	double waux_d[Nw];
	print_fxp_array_elements("\nwaux_fxp", waux, Nw);
	fxp_to_double_array(waux_d, waux, Nw);
	print_array_elements("waux", waux_d, Nw);

	int i;
	/* prepare outputs */
	double y[x_size];
	fxp32_t y_fxp[x_size];
	for (i = 0; i < x_size; i++) {
		y_fxp[i] = 0;
		y[i] = 0;
	}

	for (i = 0; i < x_size; i++) {
		shiftR(0, waux, Nw);
		y_fxp[i] = fxp_direct_form_2(waux, x_fxp[i], a_fxp, b_fxp, ds.a_size, ds.b_size);
	}

	printf("\noutputs: \n");
	print_fxp_array_elements("y_fxp", y_fxp, x_size);
	fxp_to_double_array(y, y_fxp, x_size);
	print_array_elements("y", y, x_size);

}
