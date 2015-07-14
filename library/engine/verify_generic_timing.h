/**
 * DSVerifier - Digital Systems Verifier (Timing)
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *                Iury Bessa     <iury.bessa@gmail.com>
 *
 * ------------------------------------------------------
 *
 * Verify time constraint considering generic instructions
 *
 * ------------------------------------------------------
*/

int nondet_int();
float nondet_float();

extern digital_system ds;
extern implementation impl;
extern hardware hw;

int generic_timer = 0;

int verify_generic_timing(void) {

	/* prepare initial values */
	double y[X_SIZE_VALUE];
	double x[X_SIZE_VALUE];
	int i;
	for (i = 0; i < X_SIZE_VALUE; ++i) {
		y[i] = 0;
		x[i] = nondet_float();
		__ESBMC_assume(x[i] >= impl.min && x[i] <= impl.max);
	}

	int Nw = 0;
	#if ((REALIZATION == CDFI) || (REALIZATION == CDFII) || (REALIZATION == CTDFII))
		Nw = a_cascade_size > b_cascade_size ? a_cascade_size : b_cascade_size;
	#else
		ds.a_size > ds.b_size ? ds.a_size : ds.b_size;
	#endif

	double yaux[ds.a_size];
	double xaux[ds.b_size];
	double waux[Nw];

	for (i = 0; i < ds.a_size; ++i) {
		yaux[i] = 0;
	}
	for (i = 0; i < ds.b_size; ++i) {
		xaux[i] = 0;
	}
	for (i = 0; i < Nw; ++i) {
		waux[i] = 0;
	}

	double xk, temp;
	double *aptr, *bptr, *xptr, *yptr, *wptr;

	int j;
	for (i = 0; i < X_SIZE_VALUE; ++i) {
		/* direct form I realization */
		#if (REALIZATION == DFI || REALIZATION == DDFI)
			shiftL(x[i], xaux, ds.b_size);
//			y[i] = double_direct_form_1_MSP430(yaux, xaux, ds.a, ds.b, ds.a_size, ds.b_size);
//			shiftL(y[i], yaux, ds.a_size);
		#endif

		/* direct form II realization */
//		#if (REALIZATION == DFII || REALIZATION == DDFII)
//			shiftR(0, waux, Nw);
//			y[i] = double_direct_form_2_MSP430(waux, x[i], ds.a, ds.b, ds.a_size, ds.b_size);
//		#endif

		/* transposed direct form II realization */
//		#if (REALIZATION == TDFII || REALIZATION == TDDFII)
//			y[i] = double_transposed_direct_form_2_MSP430(waux, x[i], ds.a, ds.b, ds.a_size, ds.b_size);
//		#endif

		generic_timer = 0;
	}
	return 0;
}
