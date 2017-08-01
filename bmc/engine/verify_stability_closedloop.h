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
 * verify stability in closed loop
 *
 * ------------------------------------------------------
 */

#ifndef DSVERIFIER_ENGINE_VERIFY_STABILITY_CLOSEDLOOP_H
#define DSVERIFIER_ENGINE_VERIFY_STABILITY_CLOSEDLOOP_H

extern digital_system plant;
extern digital_system plant_cbmc;
extern digital_system controller;

int verify_stability_closedloop_using_dslib(void)
{
  /* generating closed loop for series or feedback */
  double * c_num = controller.b;
  int c_num_size = controller.b_size;
  double * c_den = controller.a;
  int c_den_size = controller.a_size;

  /* quantizing controller coefficients */
#if(ARITHMETIC == FIXEDBV)
  fxp_t c_num_fxp[controller.b_size];
  fxp_double_to_fxp_array(c_num, c_num_fxp, controller.b_size);
  fxp_t c_den_fxp[controller.a_size];
  fxp_double_to_fxp_array(c_den, c_den_fxp, controller.a_size);
#elif(ARITHMETIC == FLOATBV)
  fp_t c_num_fp[controller.b_size];
  fp_double_to_fp_array(c_num, c_num_fp, controller.b_size);
  fp_t c_den_fp[controller.a_size];
  fp_double_to_fp_array(c_den, c_den_fp, controller.a_size);
#endif

  /* getting quantized controller coefficients */
#if(ARITHMETIC == FIXEDBV)
  double c_num_qtz[controller.b_size];
  fxp_to_double_array(c_num_qtz, c_num_fxp, controller.b_size);
  double c_den_qtz[controller.a_size];
  fxp_to_double_array(c_den_qtz, c_den_fxp, controller.a_size);
#elif(ARITHMETIC == FLOATBV)
  double c_num_qtz[controller.b_size];
  fp_to_double_array(c_num_qtz, c_num_fp, controller.b_size);
  double c_den_qtz[controller.a_size];
  fp_to_double_array(c_den_qtz, c_den_fp, controller.a_size);
#endif

  /* getting plant coefficients */
#if(BMC == ESBMC)
  double * p_num = plant.b;
  int p_num_size = plant.b_size;
  double * p_den = plant.a;
  int p_den_size = plant.a_size;
#elif(BMC == CBMC)
  double * p_num = plant_cbmc.b;
  int p_num_size = plant.b_size;
  double * p_den = plant_cbmc.a;
  int p_den_size = plant.a_size;
#endif

  double ans_num[MAX_DSORDER];
  int ans_num_size = controller.b_size + plant.b_size - 1;
  double ans_den[MAX_DSORDER];
  int ans_den_size = controller.a_size + plant.a_size - 1;

#if(CONNECTION_MODE == SERIES)
  ft_closedloop_series(c_num_qtz, c_num_size, c_den_qtz, c_den_size, p_num,
      p_num_size, p_den, p_den_size, ans_num, ans_num_size, ans_den,
      ans_den_size);
#elif(CONNECTION_MODE == FEEDBACK)
  printf("Verifying stability for controller\n");
  check_stability(c_den_qtz, c_den_size);
  ft_closedloop_feedback(c_num_qtz, c_num_size, c_den_qtz, c_den_size,
      p_num, p_num_size, p_den, p_den_size, ans_num,
      ans_num_size, ans_den, ans_den_size);
#endif

  /* checking stability */
  __DSVERIFIER_assert_msg(
      check_stability_closedloop(ans_den, ans_den_size, p_num, p_num_size,
          p_den, p_den_size), "check stability for closed-loop function\n");
  return 0;
}

#endif // DSVERIFIER_ENGINE_VERIFY_STABILITY_CLOSEDLOOP_H
