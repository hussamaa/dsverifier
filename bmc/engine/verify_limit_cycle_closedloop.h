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

extern digital_system plant;
extern digital_system plant_cbmc;
extern digital_system control;

double nondet_double();

int verify_limit_cycle_closed_loop(void){

	OVERFLOW_MODE = 3; /* WRAPAROUND */

	int i;
	int Set_xsize_at_least_two_times_Na = 2 * ds.a_size;
	printf("X_SIZE must be at least 2 * ds.a_size");
	__DSVERIFIER_assert(X_SIZE_VALUE >= Set_xsize_at_least_two_times_Na);

	/* generating closed loop for series or feedback */
	double * c_num = control.b;
	int c_num_size = control.b_size;
	double * c_den = control.a;
	int c_den_size = control.a_size;

	/* quantizing controller coefficients */
	fxp32_t c_num_fxp[control.b_size];
	fxp_double_to_fxp_array(c_num, c_num_fxp, control.b_size);
	fxp32_t c_den_fxp[control.a_size];
	fxp_double_to_fxp_array(c_den, c_den_fxp, control.a_size);

	/* getting quantized controller coefficients  */
	double c_num_qtz[control.b_size];
	fxp_to_double_array(c_num_qtz, c_num_fxp, control.b_size);
	double c_den_qtz[control.a_size];
	fxp_to_double_array(c_den_qtz, c_den_fxp, control.a_size);

	/* getting plant coefficients */
	#if (BMC == ESBMC)
		double * p_num = plant.b;
		int p_num_size = plant.b_size;
		double * p_den = plant.a;
		int p_den_size = plant.a_size;
	#elif (BMC == CBMC)
		double * p_num = plant_cbmc.b;
		int p_num_size = plant.b_size;
		double * p_den = plant_cbmc.a;
		int p_den_size = plant.a_size;
	#endif

	double ans_num[100];
	int ans_num_size = control.b_size + plant.b_size - 1;
	double ans_den[100];
	int ans_den_size = control.a_size + plant.a_size - 1;

	ft_closedloop_series(c_num_qtz, c_num_size, c_den_qtz, c_den_size, p_num, p_num_size, p_den, p_den_size, ans_num, ans_num_size, ans_den, ans_den_size);

	double y[X_SIZE_VALUE];
	double x[X_SIZE_VALUE];

	/* prepare inputs (all possibles values in dynamical range) */
	double xaux[ans_num_size];
	double nondet_constant_input = nondet_double();
	__DSVERIFIER_assume(nondet_constant_input >= impl.min && nondet_constant_input <= impl.max);
	for (i = 0; i < X_SIZE_VALUE; ++i) {
		x[i] = nondet_constant_input;
		y[i] = 0;
	}
	for (i = 0; i < ans_num_size; ++i) {
		xaux[i] = nondet_constant_input;
	}

	int Nw = 0;
	#if ((REALIZATION == CDFI) || (REALIZATION == CDFII) || (REALIZATION == CTDFII) || (REALIZATION == CDDFII) || (REALIZATION == CDDFII) || (REALIZATION == CTDDFII))
		Nw = a_cascade_size > b_cascade_size ? a_cascade_size : b_cascade_size;
	#else
		Nw = ans_den_size > ans_num_size ? ans_den_size : ans_num_size;
	#endif

	double yaux[ans_den_size];
	double y0[ans_den_size];

	double waux[Nw];
	double w0[Nw];

	#if (REALIZATION == DFI || REALIZATION == CDFI || REALIZATION == DDFI || REALIZATION == CDDFI)
		for (i = 0; i < ans_den_size; ++i) {
			yaux[i] = nondet_int();
			__DSVERIFIER_assume(yaux[i] >= impl.min && yaux[i] <= impl.max);
			y0[i] = yaux[i];
		}
	#else
		for (i = 0; i < Nw; ++i) {
			waux[i] = nondet_int();
			__DSVERIFIER_assume(waux[i] >= impl.min && waux[i] <= impl.max);
			w0[i] = waux[i];
		}
	#endif

	double xk, temp;
	double *aptr, *bptr, *xptr, *yptr, *wptr;

	int j;
	for(i=0; i<X_SIZE_VALUE; ++i){

		/* direct form I realization */
		#if ((REALIZATION == DFI) || (REALIZATION == DDFI))
			shiftLDouble(x[i], xaux, ans_num_size);
			y[i] = double_direct_form_1(yaux, xaux, ans_den, ans_num_size, ans_den_size, ans_num_size);
			shiftLDouble(y[i], yaux, ans_den_size);
		#endif

	}

	/* check oscillations in produced output */
	double_check_persistent_limit_cycle(y, X_SIZE_VALUE);

	return 0;
}
