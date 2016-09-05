/**
 * DSVerifier - Digital Systems Verifier (Stability)
 *
 *                Universidade Federal do Amazonas - UFAM
 *
 * Authors:       Renato Abreu   <renatobabreu@yahoo.com.br>
 *		 		  Iury Bessa     <iury.bessa@gmail.com>
 *                Hussama Ismail <hussamaismail@gmail.com>
 * ------------------------------------------------------
 *
 * Verification engine for Minimum property in digital
 * systems. This verification check if absolute value of
 * the roots of denominator are less than 1. For DFI, DFII,
 * TDFII, CDFI, CDFII, CTDFII.
 *
 * For DELTA: Currently, It is used delta criteria.
 *
 * ------------------------------------------------------
*/

extern digital_system ds;
extern implementation impl;

int verify_stability(void){

	overflow_mode = 0;

	/* check the realization */
	#if ((REALIZATION == DFI) || (REALIZATION == DFII) || (REALIZATION == TDFII))
		fxp_t a_fxp[ds.a_size];
		/* quantize the array using fxp */
		fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);
		double _a[ds.a_size];
		/* get the quantized value in double format */
		fxp_to_double_array(_a, a_fxp, ds.a_size);
		/* check stability using jury criteria */
		assert(check_stability(_a, ds.a_size));
	#elif ((REALIZATION == DDFI) || (REALIZATION == DDFII) || (REALIZATION == TDDFII))
		double da[ds.a_size];
		/* generate delta coefficients using a instrinsic function */
		generate_delta_coefficients(ds.a, da, ds.a_size, impl.delta);
		/* check stability using delta domain (intrinsic function) */
		/* assert(__DSVERIFIER_check_delta_stability(da, ds.sample_time, impl.int_bits, impl.frac_bits)); */
		printf("*** FUNCTION PENDING FOR BMC (CHECK STABILITY IN DELTA DOMAIN ***");
		assert(0);
		exit(1);
	#elif ((REALIZATION == CDFI) || (REALIZATION == CDFII)|| (REALIZATION == CTDFII))
		double a_cascade[100];
		int a_cascade_size;
		double b_cascade[100];
		int b_cascade_size;
		/* generate cascade values using a intrinsic function */
		__DSVERIFIER_generate_cascade_controllers(&ds, a_cascade, a_cascade_size, b_cascade, b_cascade_size);
		fxp_t a_cascade_fxp[100];
		/* quantize cascade using fxp library */
		fxp_double_to_fxp_array(a_cascade, a_cascade_fxp, a_cascade_size);
		double a_cascade_qtz[100];
		/* get quantized values for denominator */
		fxp_to_double_array(a_cascade_qtz, a_cascade_fxp, a_cascade_size);
		int i=0;
		double current_cascade[3];
		for( i=0; i<a_cascade_size; i=i+3 ){
			/* first element zero (remove left zeros) */
			if ((i==0) && (a_cascade_qtz[i] == 0)){
				current_cascade[0] = a_cascade_qtz[i+1];
				current_cascade[1] = a_cascade_qtz[i+2];
				assert(check_stability(current_cascade, 2));
			}else{
				current_cascade[0] = a_cascade_qtz[i];
				current_cascade[1] = a_cascade_qtz[i+1];
				current_cascade[2] = a_cascade_qtz[i+2];
				assert(check_stability(current_cascade, 3));
			}
		}
	#elif ((REALIZATION == CDDFI) || (REALIZATION == CDDFII) || (REALIZATION == CTDDFII))
		double da_cascade[100];
		/* generate delta coefficients using a instrinsic function */
		__DSVERIFIER_generate_delta_coefficients(ds.a, da_cascade, impl.delta);
		/* check stability using delta domain (intrinsic function) */
		assert(__DSVERIFIER_check_delta_stability_cascade(da_cascade, ds.sample_time, impl.int_bits, impl.frac_bits));
		exit(1);
	#endif
	return 0;
}
