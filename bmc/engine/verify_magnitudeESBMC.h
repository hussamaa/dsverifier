/**
 * DSVerifier - Digital Systems Verifier
 *
 * 				  Federal University of Amazonas - UFAM
 *
 * Authors:       Daniel Mello <dani-dmello@hotmail.com>
 *                
 * ------------------------------------------------------
 *
 * Engine needed for magnitude verification of highpass and lowpass filters
 *
 * ------------------------------------------------------
 */


extern filter_parameters filter;
extern implementation impl;
extern digital_system ds;

#define M_PI     3.14159265358979323846
#define SINE_precision 6
#define LOWPASS 1
#define HIGHPASS 2

/*
 *  Generates magnitude response from transfer function
 */
void resp_mag(double* num, int lnum, double* den, int lden, double* res, int N) {

	//__ESBMC_assume(N<110);
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

		res[i] = sqrt3(out_numRe[i] * out_numRe[i] + out_numIm[i] * out_numIm[i]); 
	    zero_test = sqrt3(out_denRe[i] * out_denRe[i] + out_denIm[i] * out_denIm[i]);
	    __DSVERIFIER_assume(zero_test != 0);
		res[i] = res[i] / zero_test;

	}
}


/*
 * Magnitude verifier 
 */



 int verify_magnitude(void) {

	int N = 100;
	double w;
	double w_incr = 1.0 / N;
  	double res[N+1];
  	int i,j;

  printf("----------------------------Coeficientes em PONTO FLUTUANTE----------------------------\n");
 /* printf("B[0]=%.20f \n", ds.b[0]);
  printf("B[0]=%.20f \n", ds.b[1]);
  printf("B[0]=%.20f \n", ds.b[2]);

  printf("B[0]=%.20f \n", ds.a[0]);
  printf("B[0]=%.20f \n", ds.a[1]);
  printf("B[0]=%.20f \n", ds.a[2]);
*/

 printf("----------------------------Resposta em PONTO FLUTUANTE----------------------------\n");

//resp_mag(ds.b, ds.b_size, ds.a, ds.a_size, res, N);

	if (1==1){
		printf("Res[0]=%.20f \n", res[0]);
		printf("Res[1]=%.20f \n", res[1]);
		printf("Res[1]=%.20f \n", res[2]);
		printf("Res[1]=%.20f \n", res[3]);
		printf("Res[1]=%.20f \n", res[4]);
		printf("Res[1]=%.20f \n", res[5]);
		printf("Res[1]=%.20f \n", res[6]);
		printf("Res[1]=%.20f \n", res[7]);
		printf("Res[1]=%.20f \n", res[8]);
		printf("Res[1]=%.20f \n", res[9]);
		printf("Res[1]=%.20f \n", res[10]);
		printf("Res[1]=%.20f \n", res[11]);
		printf("Res[1]=%.20f \n", res[12]);
		printf("Res[1]=%.20f \n", res[13]);
		printf("Res[1]=%.20f \n", res[14]);
		printf("Res[1]=%.20f \n", res[15]);
		printf("Res[1]=%.20f \n", res[16]);
		printf("Res[1]=%.20f \n", res[17]);
		printf("Res[1]=%.20f \n", res[18]);
		printf("Res[1]=%.20f \n", res[19]);
		printf("Res[1]=%.20f \n", res[20]);
		printf("Res[1]=%.20f \n", res[21]);
		printf("Res[1]=%.20f \n", res[22]);
		printf("Res[1]=%.20f \n", res[23]);
		printf("Res[1]=%.20f \n", res[24]);
		printf("Res[1]=%.20f \n", res[25]);
		printf("Res[1]=%.20f \n", res[26]);
		printf("Res[1]=%.20f \n", res[27]);
		printf("Res[1]=%.20f \n", res[28]);
		printf("Res[1]=%.20f \n", res[29]);
		printf("Res[1]=%.20f \n", res[30]);
		printf("Res[1]=%.20f \n", res[31]);
		printf("Res[1]=%.20f \n", res[32]);
		printf("Res[1]=%.20f \n", res[33]);
		printf("Res[1]=%.20f \n", res[34]);
		printf("Res[1]=%.20f \n", res[35]);
		printf("Res[1]=%.20f \n", res[36]);
		printf("Res[1]=%.20f \n", res[37]);
		printf("Res[1]=%.20f \n", res[38]);
		printf("Res[1]=%.20f \n", res[39]);
		printf("Res[1]=%.20f \n", res[40]);
		printf("Res[1]=%.20f \n", res[41]);
		printf("Res[1]=%.20f \n", res[42]);
		printf("Res[1]=%.20f \n", res[43]);
		printf("Res[1]=%.20f \n", res[44]);
		printf("Res[1]=%.20f \n", res[45]);
		printf("Res[1]=%.20f \n", res[46]);
		printf("Res[1]=%.20f \n", res[47]);
		printf("Res[1]=%.20f \n", res[48]);
		printf("Res[1]=%.20f \n", res[49]);
		printf("Res[1]=%.20f \n", res[50]);
		printf("Res[1]=%.20f \n", res[51]);
		printf("Res[1]=%.20f \n", res[52]);
		printf("Res[1]=%.20f \n", res[53]);
		printf("Res[1]=%.20f \n", res[54]);
		printf("Res[1]=%.20f \n", res[55]);
		printf("Res[1]=%.20f \n", res[56]);
		printf("Res[1]=%.20f \n", res[57]);
		printf("Res[1]=%.20f \n", res[58]);
		printf("Res[1]=%.20f \n", res[59]);
		printf("Res[1]=%.20f \n", res[60]);
		printf("Res[1]=%.20f \n", res[61]);
		printf("Res[1]=%.20f \n", res[62]);
		printf("Res[1]=%.20f \n", res[63]);
		printf("Res[1]=%.20f \n", res[64]);
		printf("Res[1]=%.20f \n", res[65]);
		printf("Res[1]=%.20f \n", res[66]);
		printf("Res[1]=%.20f \n", res[67]);
		printf("Res[1]=%.20f \n", res[68]);
		printf("Res[1]=%.20f \n", res[69]);
		printf("Res[1]=%.20f \n", res[70]);
		printf("Res[1]=%.20f \n", res[71]);
		printf("Res[1]=%.20f \n", res[72]);
		printf("Res[1]=%.20f \n", res[73]);
		printf("Res[1]=%.20f \n", res[74]);
		printf("Res[1]=%.20f \n", res[75]);
		printf("Res[1]=%.20f \n", res[76]);
		printf("Res[1]=%.20f \n", res[77]);
		printf("Res[1]=%.20f \n", res[78]);
		printf("Res[1]=%.20f \n", res[79]);
		printf("Res[1]=%.20f \n", res[80]);
		printf("Res[1]=%.20f \n", res[81]);
		printf("Res[1]=%.20f \n", res[82]);
		printf("Res[1]=%.20f \n", res[83]);
		printf("Res[1]=%.20f \n", res[84]);
		printf("Res[1]=%.20f \n", res[85]);
		printf("Res[1]=%.20f \n", res[86]);
		printf("Res[1]=%.20f \n", res[87]);
		printf("Res[1]=%.20f \n", res[88]);
		printf("Res[1]=%.20f \n", res[89]);
		printf("Res[1]=%.20f \n", res[90]);
		printf("Res[1]=%.20f \n", res[91]);
		printf("Res[1]=%.20f \n", res[92]);
		printf("Res[1]=%.20f \n", res[93]);
		printf("Res[1]=%.20f \n", res[94]);
		printf("Res[1]=%.20f \n", res[95]);
		printf("Res[1]=%.20f \n", res[96]);
		printf("Res[1]=%.20f \n", res[97]);
		printf("Res[1]=%.20f \n", res[98]);
		printf("Res[1]=%.20f \n", res[99]);
	}
  	/* quantize "a" array using fxp */

	fxp_t a_fxp[ds.a_size];
	/* quantize the array using fxp */
	fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);
	double _a[ds.a_size];
	/* get the quantized value in double format */
	fxp_to_double_array(_a, a_fxp, ds.a_size);



  	/* quantize "b" array using fxp */

	fxp_t b_fxp[ds.b_size];
	/* quantize the array using fxp */
	fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);
	double _b[ds.b_size];
	/* get the quantized value in double format */
	fxp_to_double_array(_b, b_fxp, ds.b_size);


  printf("----------------------------Coeficientes em PONTO FIXO----------------------------\n");
 /* printf("B[0]=%.20f \n", ds.b[0]);
  printf("B[0]=%.20f \n", ds.b[1]);
  printf("B[0]=%.20f \n", ds.b[2]);

  printf("B[0]=%.20f \n", ds.a[0]);
  printf("B[0]=%.20f \n", ds.a[1]);
  printf("B[0]=%.20f \n", ds.a[2]);
*/
/*
  for (i=0; i<ds.b_size; i++) {
   // ds.b[i] = fxp_to_float(fxp_float_to_fxp(ds.b[i]));
    printf("B[%d]=%.20f \n", i, ds.b[i]);
  }
  for (i=0; i<ds.a_size; i++) {
   // ds.a[i] = fxp_to_float(fxp_float_to_fxp(ds.a[i]));
    printf("A[%d]=%.20f \n", i, ds.a[i]);
  }

*/
  printf("----------------------------Resposta em PONTO FIXO----------------------------\n");

 /* generates magnitude response of the quantized TF, placing the result in the "res" array*/

  resp_mag(ds.b, ds.b_size, ds.a, ds.a_size, res, N);

	if (1==1){
		printf("Res[0]=%.20f \n", res[0]);
		printf("Res[1]=%.20f \n", res[1]);
		printf("Res[1]=%.20f \n", res[2]);
		printf("Res[1]=%.20f \n", res[3]);
		printf("Res[1]=%.20f \n", res[4]);
		printf("Res[1]=%.20f \n", res[5]);
		printf("Res[1]=%.20f \n", res[6]);
		printf("Res[1]=%.20f \n", res[7]);
		printf("Res[1]=%.20f \n", res[8]);
		printf("Res[1]=%.20f \n", res[9]);
		printf("Res[1]=%.20f \n", res[10]);
		printf("Res[1]=%.20f \n", res[11]);
		printf("Res[1]=%.20f \n", res[12]);
		printf("Res[1]=%.20f \n", res[13]);
		printf("Res[1]=%.20f \n", res[14]);
		printf("Res[1]=%.20f \n", res[15]);
		printf("Res[1]=%.20f \n", res[16]);
		printf("Res[1]=%.20f \n", res[17]);
		printf("Res[1]=%.20f \n", res[18]);
		printf("Res[1]=%.20f \n", res[19]);
		printf("Res[1]=%.20f \n", res[20]);
		printf("Res[1]=%.20f \n", res[21]);
		printf("Res[1]=%.20f \n", res[22]);
		printf("Res[1]=%.20f \n", res[23]);
		printf("Res[1]=%.20f \n", res[24]);
		printf("Res[1]=%.20f \n", res[25]);
		printf("Res[1]=%.20f \n", res[26]);
		printf("Res[1]=%.20f \n", res[27]);
		printf("Res[1]=%.20f \n", res[28]);
		printf("Res[1]=%.20f \n", res[29]);
		printf("Res[1]=%.20f \n", res[30]);
		printf("Res[1]=%.20f \n", res[31]);
		printf("Res[1]=%.20f \n", res[32]);
		printf("Res[1]=%.20f \n", res[33]);
		printf("Res[1]=%.20f \n", res[34]);
		printf("Res[1]=%.20f \n", res[35]);
		printf("Res[1]=%.20f \n", res[36]);
		printf("Res[1]=%.20f \n", res[37]);
		printf("Res[1]=%.20f \n", res[38]);
		printf("Res[1]=%.20f \n", res[39]);
		printf("Res[1]=%.20f \n", res[40]);
		printf("Res[1]=%.20f \n", res[41]);
		printf("Res[1]=%.20f \n", res[42]);
		printf("Res[1]=%.20f \n", res[43]);
		printf("Res[1]=%.20f \n", res[44]);
		printf("Res[1]=%.20f \n", res[45]);
		printf("Res[1]=%.20f \n", res[46]);
		printf("Res[1]=%.20f \n", res[47]);
		printf("Res[1]=%.20f \n", res[48]);
		printf("Res[1]=%.20f \n", res[49]);
		printf("Res[1]=%.20f \n", res[50]);
		printf("Res[1]=%.20f \n", res[51]);
		printf("Res[1]=%.20f \n", res[52]);
		printf("Res[1]=%.20f \n", res[53]);
		printf("Res[1]=%.20f \n", res[54]);
		printf("Res[1]=%.20f \n", res[55]);
		printf("Res[1]=%.20f \n", res[56]);
		printf("Res[1]=%.20f \n", res[57]);
		printf("Res[1]=%.20f \n", res[58]);
		printf("Res[1]=%.20f \n", res[59]);
		printf("Res[1]=%.20f \n", res[60]);
		printf("Res[1]=%.20f \n", res[61]);
		printf("Res[1]=%.20f \n", res[62]);
		printf("Res[1]=%.20f \n", res[63]);
		printf("Res[1]=%.20f \n", res[64]);
		printf("Res[1]=%.20f \n", res[65]);
		printf("Res[1]=%.20f \n", res[66]);
		printf("Res[1]=%.20f \n", res[67]);
		printf("Res[1]=%.20f \n", res[68]);
		printf("Res[1]=%.20f \n", res[69]);
		printf("Res[1]=%.20f \n", res[70]);
		printf("Res[1]=%.20f \n", res[71]);
		printf("Res[1]=%.20f \n", res[72]);
		printf("Res[1]=%.20f \n", res[73]);
		printf("Res[1]=%.20f \n", res[74]);
		printf("Res[1]=%.20f \n", res[75]);
		printf("Res[1]=%.20f \n", res[76]);
		printf("Res[1]=%.20f \n", res[77]);
		printf("Res[1]=%.20f \n", res[78]);
		printf("Res[1]=%.20f \n", res[79]);
		printf("Res[1]=%.20f \n", res[80]);
		printf("Res[1]=%.20f \n", res[81]);
		printf("Res[1]=%.20f \n", res[82]);
		printf("Res[1]=%.20f \n", res[83]);
		printf("Res[1]=%.20f \n", res[84]);
		printf("Res[1]=%.20f \n", res[85]);
		printf("Res[1]=%.20f \n", res[86]);
		printf("Res[1]=%.20f \n", res[87]);
		printf("Res[1]=%.20f \n", res[88]);
		printf("Res[1]=%.20f \n", res[89]);
		printf("Res[1]=%.20f \n", res[90]);
		printf("Res[1]=%.20f \n", res[91]);
		printf("Res[1]=%.20f \n", res[92]);
		printf("Res[1]=%.20f \n", res[93]);
		printf("Res[1]=%.20f \n", res[94]);
		printf("Res[1]=%.20f \n", res[95]);
		printf("Res[1]=%.20f \n", res[96]);
		printf("Res[1]=%.20f \n", res[97]);
		printf("Res[1]=%.20f \n", res[98]);
		printf("Res[1]=%.20f \n", res[99]);
	}
	/*
    for (i=0; i<N; i++) {
    printf("Res[%d]=%.20f \n", i, res[i]);
  }
	
*/
	/* generates magnitude response, placing the result in the "res" array*/

	if (filter.type == LOWPASS) { //lowpass
		for (i = 0, w = 0; (w <= 1.0); ++i, w += w_incr) {
			if (w <= filter.wp) {
				printf("1");
				__DSVERIFIER_assert_msg(res[i] >= filter.Ap, "|----------------Passband Failure-------------|");
			} else if (w == filter.wc) {
				printf("2");
				__DSVERIFIER_assert_msg(res[i] <= filter.Ac, "|-------------Cutoff Frequency Failure--------|");
			} else if ((w >= filter.wr) && (w <= 1)) {
				printf("3");
				__DSVERIFIER_assert_msg(res[i] <= filter.Ar, "|----------------Stopband Failure-------------|");
			}
		}
	} else if (filter.type == HIGHPASS) { //highpass
		for (i = 0, w = 0; (w <= 1.0); ++i, w += w_incr) {
			if (w <= filter.wr) {

					printf("B[0]=%.20f \n", ds.b[0]);
					printf("B[1]=%.20f \n", ds.b[1]);
				    printf("B[2]=%.20f \n", ds.b[2]);

					printf("B[0]=%.20f \n", ds.a[0]);
					printf("B[1]=%.20f \n", ds.a[1]);
					printf("B[2]=%.20f \n", ds.a[2]);


					printf("Res[0]=%.20f \n", res[0]);
					printf("Res[1]=%.20f \n", res[1]);

				__DSVERIFIER_assert_msg(res[i] <= filter.Ar, "|----------------Stopband Failure-------------|");
			} else if (w == filter.wc) {
				printf("5");
				__DSVERIFIER_assert_msg(res[i] <= filter.Ac, "|-------------Cutoff Frequency Failure--------|");
			} else if ((w > filter.wp) && (w <= 1)) {
				printf("6");
				__DSVERIFIER_assert_msg(res[i] >= filter.Ap, "|----------------Passband Failure-------------|");
			}
		}
	} else {

		__DSVERIFIER_assert(0);
			
	}

	return 0;
}

