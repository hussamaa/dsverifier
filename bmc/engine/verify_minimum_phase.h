/**
 * DSVerifier - Digital Systems Verifier (Minimum Phase)
 *
 *                Universidade Federal do Amazonas - UFAM
 *
 * Authors:       Renato Abreu   <renatobabreu@yahoo.com.br>
 *                                Iury Bessa     <iury.bessa@gmail.com>
 *                Hussama Ismail <hussamaismail@gmail.com>
 * ------------------------------------------------------
 *
 * Verification engine for Minimum property in digital
 * systems. This verification check if absolute value of
 * the roots of numerator are less than 1. For DFI, DFII,
 * TDFII, CDFI, CDFII, CTDFII.
 *
 * For DELTA: Currently, It is used delta criteria.
 *
 * ------------------------------------------------------
 */
#ifndef DSVERIFIER_ENGINE_MINIMUM_PHASE_H
#define DSVERIFIER_ENGINE_MINIMUM_PHASE_H

extern digital_system ds;
extern implementation impl;

int verify_minimum_phase(void)
{
  set_overflow_mode = 0;

  /* check the realization */

#if ((REALIZATION == DFI) || (REALIZATION == DFII) || (REALIZATION == TDFII))
  fxp_t b_fxp[ds.b_size];

  /* quantize the array using fxp */
  fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);

  double _b[ds.b_size];

  /* get the quantized value in double format */
  fxp_to_double_array(_b, b_fxp, ds.b_size);

  /* check stability using jury criteria */
  __DSVERIFIER_assert(check_stability(_b, ds.b_size));
#elif ((REALIZATION == DDFI) || (REALIZATION == DDFII) || (REALIZATION == TDDFII))
  double db[ds.b_size];

  /* generate delta coefficients for numerator */
  generate_delta_coefficients(ds.b, db, ds.b_size, impl.delta);

  fxp_t b_fxp[ds.b_size];

  /* quantize delta numerator using fxp */
  fxp_double_to_fxp_array(db, b_fxp, ds.b_size);

  /* __DSVERIFIER_assert(__DSVERIFIER_check_delta_stability(db, DEADLINE, impl.int_bits, impl.frac_bits)); */
  printf("*** FUNCTION PENDING FOR BMC (CHECK MINIMUM PHASE IN DELTA DOMAIN ***");
  assert(0);
  exit(1);
#elif ((REALIZATION == CDFI) || (REALIZATION == CDFII) || (REALIZATION == CTDFII))
  double a_cascade[100];
  int a_cascade_size;
  double b_cascade[100];
  int b_cascade_size;

  /* generate cascade values using a intrinsic function */
  __DSVERIFIER_generate_cascade_controllers(&ds, a_cascade, a_cascade_size, b_cascade, b_cascade_size);

  fxp_t b_cascade_fxp[100];

  /* quantize cascade using fxp library */
  fxp_double_to_fxp_array(b_cascade, b_cascade_fxp, b_cascade_size);

  double b_cascade_qtz[100];

  /* get quantized values for denominator */
  fxp_to_double_array(b_cascade_qtz, b_cascade_fxp, b_cascade_size);

  int i = 0;
  double current_cascade[3];

  for (i = 0; i < b_cascade_size; i = i + 3)
  {
    /* first element zero (remove left zeros) */
    if ((i == 0) && (b_cascade_qtz[i] == 0))
    {
      current_cascade[0] = b_cascade_qtz[i + 1];
      current_cascade[1] = b_cascade_qtz[i + 2];

      __DSVERIFIER_assert(check_stability(current_cascade, 2));
    }
    else
    {
      current_cascade[0] = b_cascade_qtz[i];
      current_cascade[1] = b_cascade_qtz[i + 1];
      current_cascade[2] = b_cascade_qtz[i + 2];

      __DSVERIFIER_assert(check_stability(current_cascade, 3));
    }
  }
#elif ((REALIZATION == CDDFI) || (REALIZATION == CDDFII) || (REALIZATION == CTDDFII))
  double db_cascade[100];

  /* generate delta coefficients using a instrinsic function */
  __DSVERIFIER_generate_delta_coefficients(ds.b, db_cascade, impl.delta);

  /* check stability using delta domain (intrinsic function) */
  __DSVERIFIER_assert(__DSVERIFIER_check_delta_stability_cascade(db_cascade, ds.sample_time, impl.int_bits,
          impl.frac_bits));
  exit(1);
#endif

  return 0;
}
#endif //DSVERIFIER_ENGINE_MINIMUM_PHASE_H
