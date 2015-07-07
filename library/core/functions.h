/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *                Iury Bessa     <iury.bessa@gmail.com>
 *                Renato Abreu   <renatobabreu@yahoo.com.br>
 *
 * ------------------------------------------------------
 *
 * common functions related to digital realization
 *
 * ------------------------------------------------------
*/

#include <assert.h>

/*==========================================================================================================================
======================================================= FUNCTIONS ==========================================================
==========================================================================================================================*/

fxp32_t shiftL(fxp32_t zIn, fxp32_t z[], int N) {
	int i;
	fxp32_t zOut;
	zOut = z[0];
	for (i = 0; i < N - 1; i++) {
		z[i] = z[i + 1];
	}
	z[N - 1] = zIn;
	return (zOut);
}

fxp32_t shiftR(fxp32_t zIn, fxp32_t z[], int N) {
	int i;
	fxp32_t zOut;
	zOut = z[N - 1];
	for (i = N - 1; i > 0; i--) {
		z[i] = z[i - 1];
	}
	z[0] = zIn;
	return zOut;
}

float shiftLfloat(float zIn, float z[], int N) {
	int i;
	float zOut;
	zOut = z[0];
	for (i = 0; i < N - 1; i++) {
		z[i] = z[i + 1];
	}
	z[N - 1] = zIn;
	return (zOut);
}

float shiftRfloat(float zIn, float z[], int N) {
	int i;
	float zOut;
	zOut = z[N - 1];
	for (i = N - 1; i > 0; i--) {
		z[i] = z[i - 1];
	}
	z[0] = zIn;
	return zOut;
}

double shiftRDdouble(double zIn, double z[], int N) {
		int i;
		double zOut;
		zOut = z[0];
		for (i = 0; i < N - 1; i++) {
			z[i] = z[i + 1];
		}
		z[N - 1] = zIn;
		return (zOut);
	}

double shiftRdouble(double zIn, double z[], int N) {
	int i;
	double zOut;
	zOut = z[N - 1];
	for (i = N - 1; i > 0; i--) {
		z[i] = z[i - 1];
	}
	z[0] = zIn;
	return zOut;
}

void shiftLboth(float zfIn, float zf[], fxp32_t zIn, fxp32_t z[], int N) {
	int i;
	fxp32_t zOut;
	float zfOut;
	zOut = z[0];
	zfOut = zf[0];
	for (i = 0; i < N - 1; i++) {
		z[i] = z[i + 1];
		zf[i] = zf[i + 1];
	}
	z[N - 1] = zIn;
	zf[N - 1] = zfIn;
}

void shiftRboth(float zfIn, float zf[], fxp32_t zIn, fxp32_t z[], int N) {
	int i;
	fxp32_t zOut;
	float zfOut;
	zOut = z[N - 1];
	zfOut = zf[N - 1];
	for (i = N - 1; i > 0; i--) {
		z[i] = z[i - 1];
		zf[i] = zf[i - 1];
	}
	z[0] = zIn;
	zf[0] = zfIn;
}

int order(int Na, int Nb) {
	return Na > Nb ? Na - 1 : Nb - 1;
}

/**
 * Calculate ln logarithm using integers with 16 bit precision
 * min: fxp_ln(0.000015259<<16)
 * max: fxp_ln(32767<<16)
 */
int fxp_ln(int x) {
	int t, y;

	y = 0xa65af;
	if (x < 0x00008000)
		x <<= 16, y -= 0xb1721;
	if (x < 0x00800000)
		x <<= 8, y -= 0x58b91;
	if (x < 0x08000000)
		x <<= 4, y -= 0x2c5c8;
	if (x < 0x20000000)
		x <<= 2, y -= 0x162e4;
	if (x < 0x40000000)
		x <<= 1, y -= 0x0b172;
	t = x + (x >> 1);
	if ((t & 0x80000000) == 0)
		x = t, y -= 0x067cd;
	t = x + (x >> 2);
	if ((t & 0x80000000) == 0)
		x = t, y -= 0x03920;
	t = x + (x >> 3);
	if ((t & 0x80000000) == 0)
		x = t, y -= 0x01e27;
	t = x + (x >> 4);
	if ((t & 0x80000000) == 0)
		x = t, y -= 0x00f85;
	t = x + (x >> 5);
	if ((t & 0x80000000) == 0)
		x = t, y -= 0x007e1;
	t = x + (x >> 6);
	if ((t & 0x80000000) == 0)
		x = t, y -= 0x003f8;
	t = x + (x >> 7);
	if ((t & 0x80000000) == 0)
		x = t, y -= 0x001fe;
	x = 0x80000000 - x;
	y -= x >> 15;
	return y;
}

/**
 * Calculate log10 logarithm using 16 bit precision
 * min: fxp_log10(0.000015259)
 * max: fxp_log10(32767.0)
 */
double fxp_log10_low(double x) {
	int xint = (int) (x * 65536.0 + 0.5);
	int lnum = fxp_ln(xint);
	int lden = fxp_ln(655360);
	return ((double) lnum / (double) lden);
}

/**
 * Calculate log10 logarithm using 16 bit precision
 * min: fxp_log10(0.000015259)
 * max: fxp_log10(2147483647.0)
 */
double fxp_log10(double x) {
	if (x > 32767.0) {
		if (x > 1073676289.0) {
			x = x / 1073676289.0;
			return fxp_log10_low(x) + 9.030873362;
		}
		x = x / 32767.0;
		return fxp_log10_low(x) + 4.515436681;
	}
	return fxp_log10_low(x);
}

float snrVariance(float s[], float n[], int blksz) {
	int i;
	double sm = 0, nm = 0, sv = 0, nv = 0, snr;
	for (i = 0; i < blksz; i++) {
		sm += s[i];
		nm += n[i];
	}
	sm /= blksz;
	nm /= blksz;
	for (i = 0; i < blksz; i++) {
		sv += (s[i] - sm) * (s[i] - sm);
		nv += (n[i] - nm) * (n[i] - nm);
	}
	if (nv != 0.0f) {
		assert(sv >= nv);
		snr = sv / nv;
		return snr;
//		assert(snr <= 2147483647.0);
//		return (10.0f * fxp_log10(snr));
	} else {
		return 9999.9f;
	}
}

float snrPower(float s[], float n[], int blksz) {
	int i;
	double sv = 0, nv = 0, snr;
	for (i = 0; i < blksz; i++) {
		sv += s[i] * s[i];
		nv += n[i] * n[i];
	}

	// Do not need to do the average before the ratio

	if (nv != 0.0f) {
		assert(sv >= nv);
		snr = sv / nv;
		return snr;
		//assert(snr <= 2147483647.0);
		//return (10.0f * fxp_log10(snr));
	} else {
		return 9999.9f;
	}
}

float snrPoint(float s[], float n[], int blksz) {
	int i;
	double ratio = 0, power = 0;
	for (i = 0; i < blksz; i++) {
		if(n[i] == 0) continue;
		ratio = s[i] / n[i];
		if(ratio > 150.0f || ratio < -150.0f) continue;
		power = ratio * ratio;
		assert(power >= 1.0f);
	}

	return 9999.9f;
}

unsigned long next = 1;
int rand(void) /* NOT RECOMMENDED (see Numerical Receipes in C) */
{
	next = next*1103515245 + 12345;
	return (unsigned int)(next/65536) % 32768;
}

void srand(unsigned int seed)
{
	next = seed;
}


//Timing data got using WCET analysis of assembly code generated by MSP430 CCS compiler
float iirOutTime(float y[], float x[], float a[], float b[], int Na, int Nb)// timer1 += 40;
{
	int timer1 = OVERHEAD;
	float *a_ptr, *y_ptr, *b_ptr, *x_ptr;									// timer1 += 8;
	float sum = 0;															// timer1 += 4;
	a_ptr = &a[1];															// timer1 += 2;
	y_ptr = &y[Na-1];														// timer1 += 13;
	b_ptr = &b[0];															// timer1 += 1;
	x_ptr = &x[Nb-1];														// timer1 += 13;
	int i, j;																// timer1 += 1;
	timer1 += 91;		//(40+42+9);
	for (i = 0; i < Nb; i++){												// timer1 += 9;
		sum += *b_ptr++ * *x_ptr--;											// timer1 += 35
		timer1 += 47;	//(12+35);
	}																		// timer1 += 12;
	for (j = 1; j < Na; j++){												// timer1 += 3;
		sum -= *a_ptr++ * *y_ptr--;											// timer1 += 37;
		timer1 += 57;	//(37+20);
	}																		// timer1 += 20;
	timer1 += 3;		//(3+7);
	assert((double)timer1*CYCLE <= (double)DEADLINE);
	return sum;																// timer1 += 7;
}

float iirIIOutTime(float w[], float x, float a[], float b[], int Na, int Nb) {// timer1 += 40;
	int timer1 = OVERHEAD;
	float *a_ptr, *b_ptr, *w_ptr;											// timer1 += 7;
	float sum = 0;															// timer1 += 4;
	a_ptr = &a[1];															// timer1 += 7;
	b_ptr = &b[0];
	w_ptr = &w[1];															// timer1 += 2;
	int k, j;																// timer1 += 2;
	timer1 += 71;	//(40+22+9)
	for (j = 1; j < Na; j++) {												// timer1 += 9;
		w[0] -= *a_ptr++ * *w_ptr++;										// timer1 += 42;
		timer1 += 54;	//(42+12)
	}																		// timer1 += 12;
	w[0] += x;																// timer1 += 21;
	w_ptr = &w[0];															// timer1 += 1;
	for (k = 0; k < Nb; k++) {												// timer1 += 9;
		sum += *b_ptr++ * *w_ptr++;											// timer1 += 34;
		timer1 += 46;	//(34+12)
	}																		// timer1 += 12;
	timer1 += 38;	//(21+1+9+7)
	assert((double)timer1*CYCLE <= (double)DEADLINE);
	return sum;																// timer1 += 7;
}

float iirIItOutTime(float w[], float x, float a[], float b[], int Na, int Nb) {// timer1 += 40;
	int timer1 = OVERHEAD;
	float *a_ptr, *b_ptr;													// timer1 += 6;
	float yout = 0;															// timer1 += 3;
	a_ptr = &a[1];															// timer1 += 7;
	b_ptr = &b[0];
	int Nw = Na > Nb ? Na : Nb;												// timer1 += 10;
	yout = (*b_ptr++ * x) + w[0];											// timer1 += 36;
	int j;
	timer1 += 105;	//(40+62+3)
	for (j = 0; j < Nw - 1; j++) {											// timer1 += 3;
		w[j] = w[j + 1];													// timer1 += 12;
		if (j < Na - 1) {													// timer1 += 9;
			w[j] -= *a_ptr++ * yout;										// timer1 += 34;
			timer1 += 41;	//(34+7)
		}																	// timer1 += 7;
		if (j < Nb - 1) {													// timer1 += 13;
			w[j] += *b_ptr++ * x;											// timer1 += 38;
			timer1 += 38;	//(38)
		}
		timer1 += 54;	//(12+9+13+20)
	}																		// timer1 += 20;
	timer1 += 7;	//(7)
	assert((double)timer1*CYCLE <= (double)DEADLINE);
	return yout;															// timer1 += 7;
}

double iirIItOutTime_double(double w[], double x, double a[], double b[], int Na, int Nb) {// timer1 += 40;
	int timer1 = OVERHEAD;
	double *a_ptr, *b_ptr;													// timer1 += 6;
	double yout = 0;															// timer1 += 3;
	a_ptr = &a[1];															// timer1 += 7;
	b_ptr = &b[0];
	int Nw = Na > Nb ? Na : Nb;												// timer1 += 10;
	yout = (*b_ptr++ * x) + w[0];											// timer1 += 36;
	int j;
	timer1 += 105;	//(40+62+3)
	for (j = 0; j < Nw - 1; j++) {											// timer1 += 3;
		w[j] = w[j + 1];													// timer1 += 12;
		if (j < Na - 1) {													// timer1 += 9;
			w[j] -= *a_ptr++ * yout;										// timer1 += 34;
			timer1 += 41;	//(34+7)
		}																	// timer1 += 7;
		if (j < Nb - 1) {													// timer1 += 13;
			w[j] += *b_ptr++ * x;											// timer1 += 38;
			timer1 += 38;	//(38)
		}
		timer1 += 54;	//(12+9+13+20)
	}																		// timer1 += 20;
	timer1 += 7;	//(7)
	assert((double)timer1*CYCLE <= (double)DEADLINE);
	return yout;															// timer1 += 7;
}

void iirOutBoth(float yf[], float xf[], float af[], float bf[], float *sumf_ref,
				fxp32_t y[], fxp32_t x[], fxp32_t a[], fxp32_t b[], fxp32_t *sum_ref, int Na, int Nb) {

	fxp32_t *a_ptr, *y_ptr, *b_ptr, *x_ptr;
	float *af_ptr, *yf_ptr, *bf_ptr, *xf_ptr;
	fxp32_t sum = 0;
	float sumf = 0;
	a_ptr = &a[1];
	y_ptr = &y[Na - 1];
	b_ptr = &b[0];
	x_ptr = &x[Nb - 1];
	af_ptr = &af[1];
	yf_ptr = &yf[Na - 1];
	bf_ptr = &bf[0];
	xf_ptr = &xf[Nb - 1];
	int i, j;

	for (i = 0; i < Nb; i++) {
		sum = fxp_add(sum, fxp_mult(*b_ptr++, *x_ptr--));
		sumf += *bf_ptr++ * *xf_ptr--;
	}

	for (j = 1; j < Na; j++) {
		sum = fxp_sub(sum, fxp_mult(*a_ptr++, *y_ptr--));
		sumf -= *af_ptr++ * *yf_ptr--;
	}
	*sum_ref = sum;
	*sumf_ref = sumf;
}

fxp32_t iirOutFixedL(fxp32_t y[], fxp32_t x[], fxp32_t xin, fxp32_t a[], fxp32_t b[], int Na,	int Nb) {
	fxp32_t *a_ptr, *y_ptr, *b_ptr, *x_ptr;
	fxp32_t sum = 0;
	a_ptr = &a[Na - 1];
	y_ptr = &y[1];
	b_ptr = &b[Nb - 1];
	x_ptr = &x[0];
	int i, j;

	for (i = 0; i < Nb - 1; i++) {
		x[i] = x[i+1];
		sum = fxp_add(sum, fxp_mult(*b_ptr--, *x_ptr++));
	}
	x[Nb - 1] = xin;
	sum = fxp_add(sum, fxp_mult(*b_ptr--, *x_ptr++));

	for (j = 1; j < Na - 1; j++) {
		sum = fxp_sub(sum, fxp_mult(*a_ptr--, *y_ptr++));
		y[j] = y[j+1];
	}
	if(Na>1) sum = fxp_sub(sum, fxp_mult(*a_ptr--, *y_ptr++));
	y[Na - 1] = sum;
	return sum;
}

float iirOutFloatL(float y[], float x[], float xin, float a[], float b[], int Na, int Nb) {
	float *a_ptr, *y_ptr, *b_ptr, *x_ptr;
	float sum = 0;
	a_ptr = &a[Na - 1];
	y_ptr = &y[1];
	b_ptr = &b[Nb - 1];
	x_ptr = &x[0];
	int i, j;

	for (i = 0; i < Nb - 1; i++) {
		x[i] = x[i+1];
		sum += *b_ptr-- * *x_ptr++;
	}
	x[Nb - 1] = xin;
	sum += *b_ptr-- * *x_ptr++;

	for (j = 1; j < Na - 1; j++) {
		sum -= *a_ptr-- * *y_ptr++;
		y[j] = y[j+1];
	}
	if(Na>1) sum -= *a_ptr-- * *y_ptr++;
	y[Na - 1] = sum;
	return sum;
}

float iirOutBothL(float yf[], float xf[], float af[], float bf[], float xfin,
		fxp32_t y[], fxp32_t x[], fxp32_t a[], fxp32_t b[], fxp32_t xin, int Na, int Nb) {
	fxp32_t *a_ptr, *y_ptr, *b_ptr, *x_ptr;
	fxp32_t sum = 0;
	a_ptr = &a[Na - 1];
	y_ptr = &y[1];
	b_ptr = &b[Nb - 1];
	x_ptr = &x[0];
	float *af_ptr, *yf_ptr, *bf_ptr, *xf_ptr;
	float sumf = 0;
	af_ptr = &af[Na - 1];
	yf_ptr = &yf[1];
	bf_ptr = &bf[Nb - 1];
	xf_ptr = &xf[0];
	int i, j;

	for (i = 0; i < Nb - 1; i++) {
		x[i] = x[i+1];
		sum = fxp_add(sum, fxp_mult(*b_ptr--, *x_ptr++));
		xf[i] = xf[i+1];
		sumf += *bf_ptr-- * *xf_ptr++;
	}
	x[Nb - 1] = xin;
	sum = fxp_add(sum, fxp_mult(*b_ptr--, *x_ptr++));
	xf[Nb - 1] = xfin;
	sumf += *bf_ptr-- * *xf_ptr++;

	for (j = 1; j < Na - 1; j++) {
		sum = fxp_sub(sum, fxp_mult(*a_ptr--, *y_ptr++));
		y[j] = y[j+1];
		sumf -= *af_ptr-- * *yf_ptr++;
		yf[j] = yf[j+1];
	}
	if(Na>1) sum = fxp_sub(sum, fxp_mult(*a_ptr--, *y_ptr++));
	y[Na - 1] = sum;
	if(Na>1) sumf -= *af_ptr-- * *yf_ptr++;
	yf[Na - 1] = sumf;
	return fxp_to_float(sum) - sumf;
}

float iirOutBothL2(float yf[], float xf[], float af[], float bf[], float xfin,
		fxp32_t y[], fxp32_t x[], fxp32_t a[], fxp32_t b[], fxp32_t xin, int Na, int Nb) {
	fxp32_t *a_ptr, *y_ptr, *b_ptr, *x_ptr;
	fxp32_t sum = 0;
	a_ptr = &a[Na - 1];
	y_ptr = &y[1];
	b_ptr = &b[Nb - 1];
	x_ptr = &x[0];
	float *af_ptr, *yf_ptr, *bf_ptr, *xf_ptr;
	float sumf = 0;
	af_ptr = &af[Na - 1];
	yf_ptr = &yf[1];
	bf_ptr = &bf[Nb - 1];
	xf_ptr = &xf[0];
	int i=0, j=1;

	for (i = 0; i < Nb - 1; i++) {
		x[i] = x[i+1];
		sum = fxp_add(sum, fxp_mult(b[Nb - 1 - i], x[i]));
		xf[i] = xf[i+1];
		sumf += bf[Nb - 1 - i] * xf[i];
	}
	x[Nb - 1] = xin;
	sum = fxp_add(sum, fxp_mult(b[Nb - 1 - i], x[i]));
	xf[Nb - 1] = xfin;
	sumf += bf[Nb - 1 - i] * xf[i];

	for (j = 1; j < Na - 1; j++) {
		sum = fxp_sub(sum, fxp_mult(a[Na - j], y[j]));
		y[j] = y[j+1];
		sumf -= af[Na - j] * yf[j];
		yf[j] = yf[j+1];
	}
	if(Na>1) sum = fxp_sub(sum, fxp_mult(a[Na - j], y[j]));
	y[Na - 1] = sum;
	if(Na>1) sumf -= af[Na - j] * yf[j];
	yf[Na - 1] = sumf;
	return fxp_to_float(sum) - sumf;
}
