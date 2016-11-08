#include <dsverifier.h>

digital_system ds = {
	.b = { -1.553, 3.119, -1.566 },
	.b_size = 3,
	.a = { 1.00000000, 0.0387300, -0.96 },
	.a_size = 3,
	.sample_time = 0.005
};

implementation impl = {
	.int_bits = 15,
	.frac_bits = 4,
	.min = -6.0,
	.max = 6.0
};

int x_size = 10;
int nondet_int();

int unit_test(){

	initialization();
	overflow_mode = 3;

	fxp_t a_fxp[ds.a_size];
	fxp_t b_fxp[ds.b_size];

	/* quantize the denominator using fxp */
	fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);
	/* quantize the numerator using fxp */
	fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);

	fxp_t min_fxp;
	fxp_t max_fxp;

	min_fxp = fxp_double_to_fxp(impl.min);
	max_fxp = fxp_double_to_fxp(impl.max);

	fxp_t y[x_size];
	fxp_t x[x_size];

	int i;
	/* prepare inputs (all possibles values in dynamical range) */
	int nondet_constant_input = nondet_int();
	__DSVERIFIER_assume(nondet_constant_input >= min_fxp && nondet_constant_input <= max_fxp);
	for (i = 0; i < x_size; ++i) {
		y[i] = 0;
		x[i] = nondet_constant_input;
	}
	fxp_t xaux[ds.b_size];
	for (i = 0; i < ds.b_size; ++i) {
		xaux[i] = nondet_constant_input;
	}

	/* prepare the previous states */
	fxp_t yaux[ds.a_size];
	fxp_t y0[ds.a_size];
	for (i = 0; i < ds.a_size; ++i) {
		yaux[i] = nondet_int();
		__DSVERIFIER_assume(yaux[i] >= min_fxp && yaux[i] <= max_fxp);
		y0[i] = yaux[i];
	}

	for(i=0; i<x_size; ++i){
		shiftL(x[i], xaux, ds.b_size);
		y[i] = fxp_direct_form_1(yaux, xaux, a_fxp, b_fxp, ds.a_size, ds.b_size);
		fxp_quant(y[i]);
		shiftL(y[i], yaux, ds.a_size);
	}

	fxp_check_exhaustively_limit_cycle(y, x_size);

}
