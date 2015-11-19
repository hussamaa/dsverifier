/**
# DSVerifier - Digital Systems Verifier (Error)
#
#                Universidade Federal do Amazonas - UFAM
#
# Authors:       Renato Abreu   <renatobabreu@yahoo.com.br>
#				 Iury Bessa     <iury.bessa@gmail.com>
#                Hussama Ismail <hussamaismail@gmail.com>
# ------------------------------------------------------
#
# For UNCERTAINTY: For use uncertainty, It's only permited
# to use DFI, DFII and TDFII forms.
#
# ------------------------------------------------------
*/

extern digital_system ds;
extern implementation impl;

int verify_error(void){

	OVERFLOW_MODE = 3;

	double a_cascade[100];
	int a_cascade_size;
	double b_cascade[100];
	int b_cascade_size;

	/* check the realization */
	#if	((REALIZATION == DFI) || (REALIZATION == DFII) || (REALIZATION == TDFII))
		fxp32_t a_fxp[ds.a_size];
		fxp32_t b_fxp[ds.b_size];
		/* quantize the denominator using fxp */
		fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);
		/* quantize the numerator using fxp */
		fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);
	#elif ((REALIZATION == DDFI)||(REALIZATION == DDFII)||(REALIZATION == TDDFII))
		double da[ds.a_size];
		double db[ds.b_size];
		get_delta_transfer_function(ds.b, db, ds.b_size,ds.a, da, ds.a_size, impl.delta);
		fxp32_t a_fxp[ds.a_size];
		fxp32_t b_fxp[ds.b_size];
		/* quantize delta denominators using fxp */
		fxp_double_to_fxp_array(da, a_fxp, ds.a_size);
		/* quantize delta numerator using fxp */
		fxp_double_to_fxp_array(db, b_fxp, ds.b_size);
	#elif ((REALIZATION == CDFI) || (REALIZATION == CDFII) || (REALIZATION == CTDFII))
		/* generate cascade realization for digital system */
		__DSVERIFIER_generate_cascade_controllers(&ds, a_cascade, a_cascade_size, b_cascade, b_cascade_size);
		fxp32_t ac_fxp[100];
		fxp32_t bc_fxp[100];
		/* quantize cascade denominators */
		fxp_double_to_fxp_array(a_cascade, ac_fxp, a_cascade_size);
		/* quantize cascade numerators */
		fxp_double_to_fxp_array(b_cascade, bc_fxp, b_cascade_size);
	#elif ((REALIZATION == CDDFI) || (REALIZATION == CDDFII) || (REALIZATION == CTDDFII))
		double da_cascade[100];
		double db_cascade[100];
		/* generate cascade realization with delta for the digital system */
		__DSVERIFIER_generate_cascade_delta_controllers(&ds, da_cascade, a_cascade_size, db_cascade, b_cascade_size, impl.delta);
		fxp32_t ac_fxp[100];
		fxp32_t bc_fxp[100];
		/* quantize cascade denominators */
		fxp_double_to_fxp_array(da_cascade, ac_fxp, a_cascade_size);
		/* quantize cascade numerators */
		fxp_double_to_fxp_array(db_cascade, bc_fxp, b_cascade_size);
	#endif

	fxp32_t min_fxp;
	fxp32_t max_fxp;

	min_fxp = fxp_double_to_fxp(impl.min);
	max_fxp = fxp_double_to_fxp(impl.max);

	///////////////////////////// STATES ///////////////////////////////
	fxp32_t y[X_SIZE_VALUE];
	fxp32_t x[X_SIZE_VALUE];
	double yf[X_SIZE_VALUE];
	double xf[X_SIZE_VALUE];
	double error[X_SIZE_VALUE];
	double snrvalue;

	int Nw = 0;

	#if ((REALIZATION == CDFI) || (REALIZATION == CDFII) || (REALIZATION == CTDFII) || (REALIZATION == CDDFII) || (REALIZATION == CDDFII) || (REALIZATION == CTDDFII))
		Nw = a_cascade_size > b_cascade_size ? a_cascade_size : b_cascade_size;
	#else
		Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;
	#endif

	fxp32_t yaux[ds.a_size];
	fxp32_t xaux[ds.b_size];
	fxp32_t waux[Nw];

	double yfaux[ds.a_size];
	double xfaux[ds.b_size];
	double wfaux[Nw];

	fxp32_t xk, temp;
	fxp32_t *aptr, *bptr, *xptr, *yptr, *wptr;

	double xkf, tempf;
	double *afptr, *bfptr, *xfptr, *yfptr, *wfptr;

	fxp32_t sum;
	double sumf;

	int i;
	for (i = 0; i < ds.a_size; ++i) {
		yaux[i] = 0;
		yfaux[i] = 0;
	}
	for (i = 0; i < ds.b_size; ++i) {
		xaux[i] = 0;
		xfaux[i] = 0;
	}
	for (i = 0; i < Nw; ++i) {
		waux[i] = 0;
		wfaux[i] = 0;
	}

	for (i = 0; i < X_SIZE_VALUE; ++i) {
		// Sorting in integer
		y[i] = 0;
		x[i] = nondet_int();
		__DSVERIFIER_assume(x[i] >= min_fxp && x[i] <= max_fxp);
		yf[i] = 0.0f;
		xf[i] = fxp_to_double(x[i]);
	}

	int j;
	for (i = 0; i < X_SIZE_VALUE; ++i) {

		#if (REALIZATION == DFI)
			/* fxp */
			shiftL(x[i], xaux, ds.b_size);
			y[i] = fxp_direct_form_1(yaux, xaux, a_fxp, b_fxp, ds.a_size, ds.b_size);
			shiftL(y[i], yaux, ds.a_size);
			/* double precision */
			shiftLDouble(xf[i], xfaux, ds.b_size);
			yf[i] = double_direct_form_1(yfaux, xfaux, ds.a, ds.b, ds.a_size, ds.b_size);
			shiftLDouble(yf[i], yfaux, ds.a_size);
		#endif

		#if (REALIZATION == DDFI)
			/* fxp */
			shiftL(x[i], xaux, ds.b_size);
			y[i] = fxp_direct_form_1(yaux, xaux, a_fxp, b_fxp, ds.a_size, ds.b_size);
			shiftL(y[i], yaux, ds.a_size);
			/* double precision */
			shiftLDouble(xf[i], xfaux, ds.b_size);
			yf[i] = double_direct_form_1(yfaux, xfaux, da, db, ds.a_size, ds.b_size);
			shiftLDouble(yf[i], yfaux, ds.a_size);
		#endif

		#if (REALIZATION == DFII)
			shiftRboth(0.0f, wfaux, 0, waux, Nw);
			y[i] = iirIIOutFixed(waux, x[i], a_fxp, b_fxp, ds.a_size, ds.b_size);
			yf[i] = iirIIOutDouble(wfaux, xf[i], ds.a, ds.b, ds.a_size, ds.b_size);
		#endif

		#if (REALIZATION == DDFII)
			shiftRboth(0.0f, wfaux, 0, waux, Nw);
			y[i] = iirIIOutFixed(waux, x[i], a_fxp, b_fxp, ds.a_size, ds.b_size);
			yf[i] = iirIIOutDouble(wfaux, xf[i], ds.a, ds.b, ds.a_size, ds.b_size);
		#endif

		#if ((REALIZATION == TDFII) || (REALIZATION == TDDFII))
			y[i] = iirIItOutFixed(waux, x[i], a_fxp, b_fxp, ds.a_size, ds.b_size);
			yf[i] = iirIItOutDouble(wfaux, xf[i], ds.a, ds.b, ds.a_size, ds.b_size);
		#endif

		/* error verification using a % setted by user */
		double error_rate = 100 - (100 * fxp_to_double(y[i]) / yf[i]);
		assert(-impl.max_error < error_rate < impl.max_error);
	}

	return 0;
}
