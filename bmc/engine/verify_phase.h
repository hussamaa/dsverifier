/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Daniel Mello <dani-dmello@hotmail.com>
 *
 * ------------------------------------------------------
 *
 * Engine needed for phase verification of filters
 *
 * ------------------------------------------------------
 */

#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <math.h>

extern filter_parameters filter;
extern implementation impl;
extern digital_system ds;
#ifndef M_PI
#define M_PI     3.14159265358979323846
#endif
#define SINE_precision 7
#define ATAN_precision 7
#define LOWPASS 1
#define HIGHPASS 2

/*
 *  Generates phase response from transfer function
 */
void resp_phase(double * num, int lnum, double * den, int lden, double * res,
	int N)
    {
    double w;
    int m, i;
    double out_numRe[N + 1], old_out_r;
    double out_numIm[N + 1];
    double out_denRe[N + 1], out_denIm[N + 1];

    for (w = 0, i = 0; w <= M_PI; w += M_PI / N, ++i)
	{
	out_numRe[i] = num[0];
	out_numIm[i] = 0;

	for (m = 1; m < lnum; ++m)
	    {
	    old_out_r = out_numRe[i];
	    out_numRe[i] = cosTyl(w, SINE_precision) * out_numRe[i]
		    - sinTyl(w, SINE_precision) * out_numIm[i] + num[m];
	    out_numIm[i] = sinTyl(w, SINE_precision) * old_out_r
		    + cosTyl(w, SINE_precision) * out_numIm[i];
	    }

	out_denRe[i] = den[0];
	out_denIm[i] = 0;

	for (m = 1; m < lden; ++m)
	    {
	    old_out_r = out_denRe[i];
	    out_denRe[i] = cosTyl(w, SINE_precision) * out_denRe[i]
		    - sinTyl(w, SINE_precision) * out_denIm[i] + den[m];
	    out_denIm[i] = sinTyl(w, SINE_precision) * old_out_r
		    + cosTyl(w, SINE_precision) * out_denIm[i];
	    }

	res[i] = atan(out_numIm[i] / out_numRe[i]);             // numerator abs
	res[i] = res[i] - atan(out_denIm[i] / out_denRe[i]);    // den abs
	}
    }

void verifyPhaseResp(double * res, double * fi, double dif, int N)
    {
    int i;
    double w;

    for (i = 0, w = 0; (w <= 1.0); ++i, w += (1.0 / N))
	{
	printf("w= %f %f\n", w, res[i]);
	printf("fi= %f %f\n", w, fi[i]);
	assert(fabs(res[i] - fi[i]) <= dif);
	}
    }

/*
 * Magnitude verifier
 */
int verify_phase(void)
    {
    rounding_mode = ROUNDING;

    int freq_response_samples = 100;
    double w;
    double w_incr = 1.0 / freq_response_samples;
    double res[freq_response_samples + 1];
    double _res[freq_response_samples + 1];
    int i, j;

    /* quantize "a" array using fxp */
    fxp_t a_fxp[ds.a_size];

    fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);

    double _a[ds.a_size];

    fxp_to_double_array(_a, a_fxp, ds.a_size);

    /* quantize "b" array using fxp */
    fxp_t b_fxp[ds.b_size];

    fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);

    double _b[ds.b_size];

    fxp_to_double_array(_b, b_fxp, ds.b_size);

    /* generates magnitude response of the quantized TF, placing the result in the "_res" array */
    resp_mag(ds.b, ds.b_size, ds.a, ds.a_size, _res, freq_response_samples);

    float dif = 0.3;

    for (i = 0, w = 0; (w <= 1.0); ++i, w += w_incr)
	{
	assert(fabs(res[i] - _res[i]) <= dif);
	}

    return 0;
    }
