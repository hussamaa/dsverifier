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

#define M_PI     3.14159265358979323846
#include "filter_functions.h"

/*
 *  Generates magnitude response from transfer function
 */
void resp_mag(double* num, int lnum, double* den, int lden, double* res, int N) {
	
	double w;
	int m, i;
	double out_numRe[N + 1], 
	double out_numIm[N + 1];
	double out_denRe[N + 1];
	double out_denIm[N + 1];
	double old_out_Re;

	for (w = 0, i = 0; w <= M_PI; w += M_PI / N, ++i) {
		out_numRe[i] = num[0];
		out_numIm[i] = 0;
		for (m = 1; m < lnum; ++m) {
			old_out_Re = out_numRe[i];
			out_numRe[i] = cos(w) * out_numRe[i] - sin(w) * out_numIm[i] + num[m];
			out_numIm[i] = sin(w) * old_out_Re + cos(w) * out_numIm[i];
		}
		out_denRe[i] = den[0];
		out_denIm[i] = 0;

		for (m = 1; m < lden; ++m) {
			old_out_Re = out_denRe[i];
			out_denRe[i] = cos(w) * out_denRe[i] - sin(w) * out_denIm[i] + den[m];
			out_denIm[i] = sin(w) * old_out_Re + cos(w) * out_denIm[i];
		}

		res[i] = sqrt(out_numRe[i] * out_numRe[i] + out_numIm[i] * out_numIm[i]); 
		res[i] = res[i] / sqrt(out_denRe[i] * out_denRe[i] + out_denIm[i] * out_denIm[i]); 

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
			out_numRe[i] = cos(w) * out_numRe[i] - sin(w) * out_numIm[i] + num[m];
			out_numIm[i] = sin(w) * old_out_r + cos(w) * out_numIm[i];
		}

		out_denRe[i] = den[0];
		out_denIm[i] = 0;
		for (m = 1; m < lden; ++m) { 
			old_out_r = out_denRe[i];
			out_denRe[i] = cos(w) * out_denRe[i] - sin(w) * out_denIm[i] + den[m];
			out_denIm[i] = sin(w) * old_out_r + cos(w) * out_denIm[i];
		}

		res[i] = atan2(out_numIm[i], out_numRe[i]); //numerator abs
		res[i] = res[i] - atan2(out_denIm[i], out_denRe[i]); //den abs
	}
}