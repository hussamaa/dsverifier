/**
 * DSVerifier - Digital Systems Verifier (Timing)
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Renato Abreu   <renatobabreu@yahoo.com.br>
 *				  Iury Bessa     <iury.bessa@gmail.com>
 *                Hussama Ismail <hussamaismail@gmail.com>
 * ------------------------------------------------------
 *
 * For UNCERTAINTY: Not supportable yet
 *
 * ------------------------------------------------------
 */

int nondet_int();
float nondet_float();

extern digital_system ds;
extern implementation impl;

int verify_timing_msp_430(void)
{

	/* prepare initial values */
	double y[X_SIZE_VALUE];
	double x[X_SIZE_VALUE];
	int i;
	for (i = 0; i < X_SIZE_VALUE; ++i)
	{
		y[i] = 0;
		x[i] = nondet_float();
		__DSVERIFIER_assume(x[i] >= impl.min && x[i] <= impl.max);
	}

	int Nw = 0;
#if ((REALIZATION == CDFI) || (REALIZATION == CDFII) || (REALIZATION == CTDFII))
	Nw = a_cascade_size > b_cascade_size ? a_cascade_size : b_cascade_size;
#else
	Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;
#endif

	double yaux[ds.a_size];
	double xaux[ds.b_size];
	double waux[Nw];

	for (i = 0; i < ds.a_size; ++i)
	{
		yaux[i] = 0;
	}
	for (i = 0; i < ds.b_size; ++i)
	{
		xaux[i] = 0;
	}
	for (i = 0; i < Nw; ++i)
	{
		waux[i] = 0;
	}

	double xk, temp;
	double *aptr, *bptr, *xptr, *yptr, *wptr;

	int j;
	for (i = 0; i < X_SIZE_VALUE; ++i)
	{
		/* direct form I realization */
#if (REALIZATION == DFI || REALIZATION == DDFI)
		shiftL(x[i], xaux, ds.b_size);
		y[i] = double_direct_form_1_MSP430(yaux, xaux, ds.a, ds.b, ds.a_size,
				ds.b_size);
		shiftL(y[i], yaux, ds.a_size);
#endif

		/* direct form II realization */
#if (REALIZATION == DFII || REALIZATION == DDFII)
		shiftR(0, waux, Nw);
		y[i] = double_direct_form_2_MSP430(waux, x[i], ds.a, ds.b, ds.a_size,
				ds.b_size);
#endif

		/* transposed direct form II realization */
#if (REALIZATION == TDFII || REALIZATION == TDDFII)
		y[i] = double_transposed_direct_form_2_MSP430(waux, x[i], ds.a, ds.b,
				ds.a_size, ds.b_size);
#endif

		/* cascade direct form I realization (or delta cascade) */
#if ((REALIZATION == CDFI) || (REALIZATION == CDDFI))
		assert((Nw % 3) == 0 && a_cascade_size == b_cascade_size); //Necessary for this implementation of cascaded filters
		xk = x[i];
		for (j = 0; j < a_cascade_size; j += 3)
		{
			aptr = &a_cascade[j];
			bptr = &b_cascade[j];
			xptr = &xaux[j];
			yptr = &yaux[j];
			shiftL(xk, xptr, 3);
			y[i] = double_direct_form_1_MSP430(yptr, xptr, aptr, bptr, 3, 3);
			shiftL(y[i], yptr, 3);
			xk = y[i];
		}
#endif

		/* cascade direct form II realization (or delta cascade) */
#if ((REALIZATION == CDFII) || (REALIZATION == CDDFII))
		assert((Nw % 3) == 0 && a_cascade_size == b_cascade_size);
		xk = x[i];
		for (j = 0; j < Nw; j += 3)
		{
			aptr = &a_cascade[j];
			bptr = &b_cascade[j];
			wptr = &waux[j];
			shiftR(0, wptr, 3);
			y[i] = double_direct_form_2_MSP430(wptr, xk, aptr, bptr, 3, 3);
			xk = y[i];
		}
#endif

		/* cascade transposed direct form II realization (or delta cascade) */
#if ((REALIZATION == CTDFII) || (REALIZATION == CTDDFII))
		assert((Nw % 3) == 0 && a_cascade_size == b_cascade_size);
		xk = x[i];
		for (j = 0; j < Nw; j += 3)
		{
			aptr = &a_cascade[j];
			bptr = &b_cascade[j];
			wptr = &waux[j];
			y[i] = double_transposed_direct_form_2_MSP430(wptr, xk, aptr, bptr,
					3, 3);
			xk = y[i];
		}
#endif

	}
	return 0;
}
