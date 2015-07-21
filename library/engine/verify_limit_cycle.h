/**
 * DSVerifier - Digital Systems Verifier (Limit Cycle)
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *
 * ------------------------------------------------------
 *
 * ------------------------------------------------------
*/

extern digital_system ds;
extern implementation impl;

int verify_limit_cycle(void){

	OVERFLOW_MODE = 3; /* WRAPAROUND */

	int i;
	int Set_xsize_at_least_two_times_Na = 2 * ds.a_size;
	printf("X_SIZE must be at least 2 * ds.a_size");
	assert(X_SIZE_VALUE >= Set_xsize_at_least_two_times_Na);

	fxp32_t a_fxp[ds.a_size];
	fxp32_t b_fxp[ds.b_size];

	/* quantize the denominator using fxp */
	fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);
	/* quantize the numerator using fxp */
	fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);

	fxp32_t min_fxp;
	fxp32_t max_fxp;

	min_fxp = fxp_double_to_fxp(impl.min);
	max_fxp = fxp_double_to_fxp(impl.max);

	fxp32_t y[X_SIZE_VALUE];
	fxp32_t x[X_SIZE_VALUE];

	int nondet_constant_input = nondet_int();
	__ESBMC_assume(nondet_constant_input >= min_fxp && nondet_constant_input <= max_fxp);

	/* prepare inputs (all possibles values in dynamical range) */
	for (i = 0; i < X_SIZE_VALUE; ++i) {
		y[i] = 0;
		x[i] = nondet_constant_input;
	}

	int Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;

	fxp32_t yaux[ds.a_size];
	fxp32_t xaux[ds.b_size];
	fxp32_t waux[Nw];

	fxp32_t y0[ds.a_size];

	for (i = 0; i < ds.a_size; ++i) {
		yaux[i] = nondet_int();
		__ESBMC_assume(yaux[i] >= min_fxp && yaux[i] <= max_fxp);
		y0[i] = yaux[i]; /* stores initial value for later comparison */
	}

	for (i = 0; i < ds.b_size; ++i) {
		xaux[i] = 0;
	}

	int j;
	int count = 0;
	int not_nondet_constant_input = 0;
	int window = 2; /* window size */

	fxp32_t xk;
	fxp32_t *aptr, *bptr, *xptr, *yptr, *wptr;

	int VALOR_X = 0;
	for(i=0; i<X_SIZE_VALUE; ++i){
		/* direct form I realization */
		shiftL(x[i],xaux,ds.b_size);
		y[i] = fxp_direct_form_1(yaux, xaux, a_fxp, b_fxp, ds.a_size, ds.b_size);
		shiftL(y[i],yaux,ds.a_size);
	}

	/* found cycle limit */
	int window_timer = 0;
	int window_count = 0;
	for (i = 2; i < X_SIZE_VALUE/2; i++){ /* check this condition */
		int window_size = i;
		for(j=0; j<X_SIZE_VALUE; j++){
			if (window_timer > window_size){
				window_timer = 0;
				window_count = 0;
			}
			/* check bound of outputs */
			int window_index = j + window_size;
			if (window_index < X_SIZE_VALUE){
				/* check if window occurr */
				if (y[j] == y[window_index] && (y[j] != y[j+1])){
					window_count++;
					assert(!(window_count == window_size));
				}
			}else{
				break;
			}
			window_timer++;
		}
	}

	return 0;
}
