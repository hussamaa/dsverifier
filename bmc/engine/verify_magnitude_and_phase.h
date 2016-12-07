/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Daniel Mello <dani-dmello@hotmail.com>
 *                
 * ------------------------------------------------------
 *
 * functions needed for magnitude and phase verification
 *
 * ------------------------------------------------------
 */
#include <stdio.h>
#include <stdint.h>
#include "/home/daniel/dsverifier/dsverifier/bmc/core/filter_functions.h"
#include <assert.h>


//filter_parameters prop;
//implementation impl;
//digital_system ds;

extern filter_parameters prop;
extern implementation impl;
extern digital_system ds;

#define M_PI     3.14159265358979323846
#define SINE_precision 4
#define ATAN_precision 6
//#include "filter_functions.h"

/*
 *  Generates magnitude response from transfer function
 */
void resp_mag(double* num, int lnum, double* den, int lden, double* res, int N) {
	
	double w;
	int m, i;
	double out_numRe[N + 1];
	double out_numIm[N + 1];
	double out_denRe[N + 1];
	double out_denIm[N + 1];
	double old_out_Re;
	double zero_test;
	for (w = 0, i = 0; w <= M_PI; w += M_PI / N, ++i) {
		out_numRe[i] = num[0];
		out_numIm[i] = 0;
		for (m = 1; m < lnum; ++m) {
			old_out_Re = out_numRe[i];
			out_numRe[i] = cosTyl(w, SINE_precision) * out_numRe[i] - sinTyl(w, SINE_precision) * out_numIm[i] + num[m];
			out_numIm[i] = sinTyl(w, SINE_precision) * old_out_Re + cosTyl(w, SINE_precision) * out_numIm[i];
		}
		out_denRe[i] = den[0];
		out_denIm[i] = 0;

		for (m = 1; m < lden; ++m) {
			old_out_Re = out_denRe[i];
			out_denRe[i] = cosTyl(w, SINE_precision) * out_denRe[i] - sinTyl(w, SINE_precision) * out_denIm[i] + den[m];
			out_denIm[i] = sinTyl(w, SINE_precision) * old_out_Re + cosTyl(w, SINE_precision) * out_denIm[i];
		}

		res[i] = (double)sqrt3(out_numRe[i] * out_numRe[i] + out_numIm[i] * out_numIm[i]); 
	    

	    zero_test = sqrt3(out_denRe[i] * out_denRe[i] + out_denIm[i] * out_denIm[i]);
	   	//if (zero_test != 0)
		res[i] = (double)res[i] / zero_test;
		//else 
		//res[i] = (double)res[i] / 1E-5;	

	}
}

/*
 *  Generates phase response from transfer function
 */
void resp_phase(double* num, int lnum, double* den, int lden, double* res, int N) {
	
	double w;
	int m, i;
	double out_numRe[N + 1], old_out_r;
	double out_numIm[N + 1];
	double out_denRe[N + 1], out_denIm[N + 1];
	for (w = 0, i = 0; w <= M_PI; w += M_PI / N, ++i) {
		out_numRe[i] = num[0];
		out_numIm[i] = 0;
		for (m = 1; m < lnum; ++m) {
			old_out_r = out_numRe[i];
			out_numRe[i] = cosTyl(w, SINE_precision) * out_numRe[i] - sinTyl(w, SINE_precision) * out_numIm[i] + num[m];
			out_numIm[i] = sinTyl(w, SINE_precision) * old_out_r + cosTyl(w, SINE_precision) * out_numIm[i];
		}

		out_denRe[i] = den[0];
		out_denIm[i] = 0;
		for (m = 1; m < lden; ++m) { 
			old_out_r = out_denRe[i];
			out_denRe[i] = cosTyl(w, SINE_precision) * out_denRe[i] - sinTyl(w, SINE_precision) * out_denIm[i] + den[m];
			out_denIm[i] = sinTyl(w, SINE_precision) * old_out_r + cosTyl(w, SINE_precision) * out_denIm[i];
		}

		res[i] = atanTyl(out_numIm[i]/out_numRe[i], ATAN_precision); //numerator abs
		res[i] = res[i] - atanTyl(out_denIm[i]/out_denRe[i], ATAN_precision); //den abs
	}
}


/*
 * Magnitude verifier 
 */


 void verify_magnitude(filter_parameters prop, double *res , int N) {

	int i;
	double w;
	double w_incr = 1.0 / N;

	if (prop.type == 1) { //lowpass
		for (i = 0, w = 0; (w <= 1.0); ++i, w += w_incr) {
			if (w <= prop.wp) {
				__ESBMC_assert(res[i] >= prop.Ap, "|----------------Passband Failure-------------|");
			} else if (w == prop.wc) {
				__ESBMC_assert(res[i] <= prop.Ac, "|-------------Cutoff Frequency Failure--------|");
			} else if ((w >= prop.wr) && (w <= 1)) {
				__ESBMC_assert(res[i] <= prop.Ar, "|----------------Stopband Failure-------------|");
			}
		}
	} else if (prop.type == 2) { //highpass
		for (i = 0, w = 0; (w <= 1.0); ++i, w += w_incr) {
			if (w <= prop.wr) {
				__ESBMC_assert(res[i] <= prop.Ar, "|----------------Stopband Failure-------------|");
			} else if (w == prop.wc) {
				__ESBMC_assert(res[i] <= prop.Ac, "|-------------Cutoff Frequency Failure--------|");
			} else if ((w > prop.wp) && (w <= 1)) {
				__ESBMC_assert(res[i] >= prop.Ap, "|----------------Passband Failure-------------|");
			}
		}
	} else {

		//assert(0); //Filter type not supported
	}




/*
 void verify_magnitude(filter_parameters prop, double *res , int N) {

	int i;
	double w;
	double w_incr = 1.0 / N;

	if (prop.type == 1) { //lowpass
		for (i = 0, w = 0; (w <= 1.0); ++i, w += w_incr) {
			if (w <= prop.wp) {				
				assert(res[i] >= prop.Ap);
			} else if (w == prop.wc) {				
				assert(res[i] <= prop.Ac);
			} else if ((w >= prop.wr) && (w <= 1)) {
				assert(res[i] <= prop.Ar);
			}
		}
	} else if (prop.type == 2) { //highpass
		for (i = 0, w = 0; (w <= 1.0); ++i, w += w_incr) {
			if (w <= prop.wr) {
				assert(res[i] <= prop.Ar);
			} else if (w == prop.wc) {
				assert(res[i] <= prop.Ac);
			} else if ((w > prop.wp) && (w <= 1)) {
				assert(res[i] >= prop.Ap);
			}
		}
	} else {

		//assert(0); //Filter type not supported
	}

*/
}

