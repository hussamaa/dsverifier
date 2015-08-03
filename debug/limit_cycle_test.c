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

digital_system ds = {
	.b = { 1.5, -0.5 },
	.b_size = 2,
	.a = { 1.0 },
	.a_size = 1
};

implementation impl = {
	.int_bits = 2,
	.frac_bits = 14,
	.min = -1.0,
	.max = 1.0
};

hardware hw = { };

/* inputs */
fxp32_t x[25] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0  };
int x_size = 25;

int generic_timer;

/** function to set the necessary parameters to DSVerifier FXP library */
void init(){
	if (impl.frac_bits >= FXP_WIDTH){
		printf("impl.frac_bits must be less than word width!\n");
	}
	if (impl.int_bits >= FXP_WIDTH - impl.frac_bits){
	   printf("impl.int_bits must be less than word width subtracted by precision!\n");
	   assert(0);
	}
	if(impl.frac_bits >= 31){
		_fxp_one = 0x7fffffff;
	}else{
		_fxp_one = (0x00000001 << impl.frac_bits);
	}

	_fxp_half      = (0x00000001 << (impl.frac_bits - 1));
	_fxp_minus_one = -(0x00000001 << impl.frac_bits);
	_fxp_min       = -(0x00000001 << (impl.frac_bits + impl.int_bits - 1));
	_fxp_max       = (0x00000001 << (impl.frac_bits + impl.int_bits - 1)) - 1;
	_fxp_fmask     = ((((int32_t) 1) << impl.frac_bits) - 1);
	_fxp_imask     = ((0x80000000) >> (FXP_WIDTH - impl.frac_bits - 1));

	int i = 0;
	/* applying scale in numerator coefficients */
	if ((impl.scale == 0) || (impl.scale == 1)){
		impl.scale = 1;
		return;
	}
	if (PROPERTY != STABILITY_CLOSED_LOOP){
		if (ds.b_size > 0){
			for(i = 0; i < ds.b_size; i++)
				ds.b[i] = ds.b[i] / impl.scale;
		}
	}
}

int main(){
	
	init();

	OVERFLOW_MODE = 3;

	printf("original coefficients: \n");
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
	fxp32_t w0[Nw];
	fxp32_t waux[Nw];
	waux[0] = -16384;
	w0[0] = -16384;
	w0[1] = 123;

	int i, j;
	/* prepare outputs */
	fxp32_t y_fxp[x_size];
	double y[x_size];
	for (i = 0; i < x_size; i++) {
		y_fxp[i] = 0;
		y[i] = 0;
	}

	fxp32_t xk;
	fxp32_t *aptr, *bptr, *xptr, *yptr, *wptr;
	int count = 0;
	int notzeros = 0;

	for (i = 0; i < x_size; i++) {

		y_fxp[i] = fxp_transposed_direct_form_2(waux, x[i], a_fxp, b_fxp, ds.a_size, ds.b_size);

		for (j = Nw - 1; j >= 0; --j) {
			printf("\nwaux[%d] (%d) == w0[%d] (%d)\n",j, waux[j], j, w0[j]);
			if (waux[j] == w0[j]) {
				printf("count ++\n");
				++count;
			}
			if (waux[j] != 0) {
				printf("notzeros ++\n");
				++notzeros;
			}
		}
		if (notzeros != 0) {
			printf("count < Nw ----> %d < %d\n", count, Nw);
			assert(count < Nw);
		}

		count = 0;
		notzeros = 0;

	}

	printf("\noutputs: \n");
	fxp_to_double_array(y, y_fxp, x_size);
	print_fxp_array_elements("y_fxp", y_fxp, x_size);
	print_array_elements("\ny", y, x_size);

}
