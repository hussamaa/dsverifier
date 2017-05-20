/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Daniel Mello <dani-dmello@hotmail.com>
 *                
 * ------------------------------------------------------
 *
 * Engine needed for magnitude verification of highpass and lowpass filters
 *
 * ------------------------------------------------------
 */

#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <math.h>
#include "../core/definitions.h"

extern filter_parameters filter;
extern implementation impl;
extern digital_system ds;

#define M_PI     3.14159265358979323846
#define SINE_precision 7
#define LOWPASS 1
#define HIGHPASS 2
#define PASSBAND 3

/*
 *  Generates magnitude response from transfer function
 */
void resp_mag(double* num, int lnum, double* den, int lden, double* res, int N)
{

	double w;
	int m, i;
	double out_numRe[N + 1];
	double out_numIm[N + 1];
	double out_denRe[N + 1];
	double out_denIm[N + 1];
	double old_out_Re;
	double zero_test;
	for (w = 0, i = 0; w <= M_PI; w += M_PI / N, ++i)
	{
		out_numRe[i] = num[0];
		out_numIm[i] = 0;
		for (m = 1; m < lnum; ++m)
		{
			old_out_Re = out_numRe[i];
			out_numRe[i] = cosTyl(w, SINE_precision) * out_numRe[i]
					- sinTyl(w, SINE_precision) * out_numIm[i] + num[m];
			out_numIm[i] = sinTyl(w, SINE_precision) * old_out_Re
					+ cosTyl(w, SINE_precision) * out_numIm[i];
		}
		out_denRe[i] = den[0];
		out_denIm[i] = 0;

		for (m = 1; m < lden; ++m)
		{
			old_out_Re = out_denRe[i];
			out_denRe[i] = cosTyl(w, SINE_precision) * out_denRe[i]
					- sinTyl(w, SINE_precision) * out_denIm[i] + den[m];
			out_denIm[i] = sinTyl(w, SINE_precision) * old_out_Re
					+ cosTyl(w, SINE_precision) * out_denIm[i];
		}

		res[i] = sqrt(
				out_numRe[i] * out_numRe[i] + out_numIm[i] * out_numIm[i]);
		zero_test = sqrt(
				out_denRe[i] * out_denRe[i] + out_denIm[i] * out_denIm[i]);
		res[i] = res[i] / zero_test;
	}
}

/*
 * Magnitude verifier 
 */
int verify_magnitude(void)
{

	rounding_mode = ROUNDING;

	int freq_response_samples = 100;
	double w;
	double w_incr = 1.0 / freq_response_samples;
	double _res[freq_response_samples + 1];
	int i, j;
	char msg[50];

	/*quantization of the floating point transfer function coefficients */
	for (i = 0; i < ds.b_size; i++)
	{
		ds.b[i] = fxp_to_double(fxp_double_to_fxp(ds.b[i]));
	}
	for (i = 0; i < ds.a_size; i++)
	{
		ds.a[i] = fxp_to_double(fxp_double_to_fxp(ds.a[i]));
	}

	/* generates magnitude response of the quantized TF, placing the result in the "_res" array*/
	resp_mag(ds.b, ds.b_size, ds.a, ds.a_size, _res, freq_response_samples);

	if ((filter.wp == 0) && (filter.wr == 0))
	{

		if (filter.type == LOWPASS)
		{
			filter.wp = filter.wc - w_incr;
			filter.wr = filter.wc + w_incr;
		}

		if (filter.type == HIGHPASS)
		{
			filter.wp = filter.wc + w_incr;
			filter.wr = filter.wc - w_incr;
		}
	}

	if (filter.type == LOWPASS)
	{

		if (filter.Ar == 0)
			filter.Ar = 1;

		for (i = 0, w = 0; (w <= 1.0); ++i, w += w_incr)
		{

			if ((w < filter.wp) || (doubleComparisson(filter.wp, w, 0.0000001)))
			{
				assert(_res[i] >= filter.Ap);
			}
			if (doubleComparisson(filter.wc, w, 0.000001) && (filter.wc != 0))
			{
				assert((_res[i]) < (filter.Ac));
			}
			if (((w > filter.wr) || (doubleComparisson(filter.wr, w, 0.0000001)))
					&& (w <= 1) && (filter.wr != 0))
			{
				assert(_res[i] <= filter.Ar);
			}
		}
	}
	else if (filter.type == HIGHPASS)
	{

		if (filter.Ar == 0)
			filter.Ar = 1;

		for (i = 0, w = 0; (w <= 1.0); ++i, w += w_incr)
		{

			if ((w < filter.wr) || (doubleComparisson(filter.wr, w, 0.0000001)))
			{
				assert(_res[i] <= filter.Ar);
			}
			if (doubleComparisson(filter.wc, w, 0.0000001) && (filter.wc != 0))
			{
				assert((_res[i]) < (filter.Ac));
			}
			if (((w > filter.wp) || (doubleComparisson(filter.wp, w, 0.0000001)))
					&& (w <= 1) && (filter.wr != 0))
			{
				assert(_res[i] >= filter.Ap);
			}
		}
	}
	else if (filter.type == PASSBAND)
	{

		if (filter.Ar == 0)
			filter.Ar = 1;

		for (i = 0, w = 0; (w <= 1.0); ++i, w += w_incr)
		{

			if (((w < filter.w1r)
					|| (doubleComparisson(filter.w1r, w, 0.0000001)))
					&& (filter.w1r != 0))
			{
				assert(_res[i] <= filter.Ar);

			}
			if (((w < filter.w1c)
					|| (doubleComparisson(filter.w1c, w, 0.0000001)))
					&& ((w > (filter.w1c - w_incr))
							|| (doubleComparisson(filter.w1c - w_incr, w,
									0.0000001))) && (filter.w1c != 0))
			{
				assert(_res[i] <= filter.Ac);

			}
			if (((w > filter.w1p)
					|| (doubleComparisson(filter.w1p, w, 0.0000001)))
					&& ((w < filter.w2p)
							|| (doubleComparisson(filter.w2p, w, 0.0000001))))
			{
				assert(_res[i] >= filter.Ap);

			}
			if (((w > filter.w2c)
					|| (doubleComparisson(filter.w2c, w, 0.0000001)))
					&& (w < (filter.w2c + w_incr)
							|| (doubleComparisson(filter.w2c + w_incr, w,
									0.0000001))) && (filter.w2c != 0))
			{
				assert(_res[i] <= filter.Ac);

			}
			if (((w > filter.w2r)) && (w <= 1) && (filter.w2r != 0))
			{
				assert(_res[i] <= filter.Ar);
			}
		}
	}
	else
	{
		assert(0);
	}

	return 0;
}
