/**
 * DSVerifier - Digital Systems Verifier (Zero Input Limit Cycle)
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

int verify_zero_input_limit_cycle(void){

	OVERFLOW_MODE = 3; /* WRAPAROUND */

	int i,j;
	int Set_xsize_at_least_two_times_Na = 2 * ds.a_size;
	printf("X_SIZE must be at least 2 * ds.a_size");
	assert(X_SIZE_VALUE >= Set_xsize_at_least_two_times_Na);

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
		get_delta_transfer_function_with_base(ds.b, db, ds.b_size,ds.a, da, ds.a_size, impl.delta);
		fxp32_t a_fxp[ds.a_size];
		fxp32_t b_fxp[ds.b_size];
		/* quantize delta denominators using fxp */
		fxp_double_to_fxp_array(da, a_fxp, ds.a_size);
		/* quantize delta numerator using fxp */
		fxp_double_to_fxp_array(db, b_fxp, ds.b_size);
	#elif ((REALIZATION == CDFI) || (REALIZATION == CDFII) || (REALIZATION == CTDFII))
		double a_cascade[100];
		int a_cascade_size;
		double b_cascade[100];
		int b_cascade_size;
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
		int a_cascade_size;
		double db_cascade[100];
		int b_cascade_size;
		/* generate cascade realization with delta for the digital system */
		__DSVERIFIER_generate_cascade_delta_controllers(&ds, da_cascade, a_cascade_size, db_cascade, b_cascade_size, impl.delta);
		fxp32_t ac_fxp[100];
		fxp32_t bc_fxp[100];
		/* quantize cascade denominators */
		fxp_double_to_fxp_array(da_cascade, ac_fxp, a_cascade_size);
		/* quantize cascade numerators */
		fxp_double_to_fxp_array(db_cascade, bc_fxp, b_cascade_size);
	#endif

	fxp32_t min_fxp = fxp_double_to_fxp(impl.min);
	fxp32_t max_fxp = fxp_double_to_fxp(impl.max);

	fxp32_t y[X_SIZE_VALUE];
	fxp32_t x[X_SIZE_VALUE];

	/* prepare zero inputs */
	for (i = 0; i < X_SIZE_VALUE; ++i) {
		y[i] = 0;
		x[i] = 0;
	}

	int Nw = 0;
	#if ((REALIZATION == CDFI) || (REALIZATION == CDFII) || (REALIZATION == CTDFII) || (REALIZATION == CDDFII) || (REALIZATION == CDDFII) || (REALIZATION == CTDDFII))
		Nw = a_cascade_size > b_cascade_size ? a_cascade_size : b_cascade_size;
	#else
		Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;
	#endif

	fxp32_t yaux[ds.a_size];
	fxp32_t xaux[ds.b_size];
	fxp32_t waux[Nw];

	fxp32_t y0[ds.a_size];
	fxp32_t w0[Nw];

	#if (REALIZATION == DFI || REALIZATION == CDFI || REALIZATION == DDFI || REALIZATION == CDDFI)
		for (i = 0; i < ds.a_size; ++i) {
			yaux[i] = nondet_int();
			__DSVERIFIER_assume(yaux[i] >= min_fxp && yaux[i] <= max_fxp);
			y0[i] = yaux[i];
		}
	#else
		for (i = 0; i < Nw; ++i) {
			waux[i] = nondet_int();
			__DSVERIFIER_assume(waux[i] >= min_fxp && waux[i] <= max_fxp);
			w0[i] = waux[i];
		}
	#endif

	for (i = 0; i < ds.b_size; ++i) {
		xaux[i] = 0;
	}

	fxp32_t xk, temp;
	fxp32_t *aptr, *bptr, *xptr, *yptr, *wptr;

	for(i=0; i<X_SIZE_VALUE; ++i){

		/* direct form I realization */
		#if ((REALIZATION == DFI) || (REALIZATION == DDFI))
			shiftL(x[i], xaux, ds.b_size);
			y[i] = fxp_direct_form_1(yaux, xaux, a_fxp, b_fxp, ds.a_size, ds.b_size);
			#ifdef JACKSON_RULE
				fxp_quant(y[i]);
			#endif
			shiftL(y[i], yaux, ds.a_size);
		#endif

		/* direct form II realization */
		#if ((REALIZATION == DFII) || (REALIZATION == DDFII))
			shiftR(0, waux, Nw);
			y[i] = fxp_direct_form_2(waux, x[i], a_fxp, b_fxp, ds.a_size, ds.b_size);
			#ifdef JACKSON_RULE
				fxp_quant(y[i]);
			#endif
		#endif

		/* transposed direct form II realization */
		#if ((REALIZATION == TDFII) || (REALIZATION ==TDDFII))
			y[i] = fxp_transposed_direct_form_2(waux, x[i], a_fxp, b_fxp, ds.a_size, ds.b_size);
			#ifdef JACKSON_RULE
				fxp_quant(y[i]);
			#endif
		#endif

		/* cascade direct form I realization (or delta cascade) */
		#if ((REALIZATION == CDFI) || (REALIZATION == CDDFI))
			assert((Nw % 3) == 0 && a_cascade_size == b_cascade_size);
			xk = x[i];
			for (j = 0; j < a_cascade_size; j += 3) {
				aptr = &ac_fxp[j];
				bptr = &bc_fxp[j];
				xptr = &xaux[j];
				yptr = &yaux[j];
				shiftL(xk, xptr, 3);
				y[i] = fxp_direct_form_1(yptr, xptr, aptr, bptr, 3, 3);
				shiftL(y[i], yptr, 3);
				xk = y[i];
			}
		#endif

		/* cascade direct form II realization (or delta cascade) */
		#if ((REALIZATION == CDFII) || (REALIZATION == CDDFII))
			assert((Nw % 3) == 0 && a_cascade_size == b_cascade_size);
			for (j = 0; j < a_cascade_size; j += 3) {
				aptr = &ac_fxp[j];
				bptr = &bc_fxp[j];
				wptr = &waux[j];
				shiftR(0, wptr, 3);
				y[i] = fxp_direct_form_2(wptr, xk, aptr, bptr, 3, 3);
				xk = y[i];
			}
		#endif

		/* cascade transposed direct form II realization (or delta cascade) */
		#if ((REALIZATION == CTDFII) || (REALIZATION == CTDDFII))
			assert((Nw % 3) == 0 && a_cascade_size == b_cascade_size);
			xk = x[i];
			for (j = 0; j < a_cascade_size; j += 3) {
				aptr = &ac_fxp[j];
				bptr = &bc_fxp[j];
				wptr = &waux[j];
				y[i] = fxp_transposed_direct_form_2(wptr, xk, aptr, bptr, 3, 3);
				xk = y[i];
			}
		#endif
	}

	/* check oscillations in produced output */
	fxp_check_persistent_limit_cycle(y, X_SIZE_VALUE);

	return 0;
}
