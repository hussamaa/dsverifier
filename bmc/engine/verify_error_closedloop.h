/**
 * DSVerifier - Digital Systems Verifier (Quantization Error in Closed-loop)
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *
 * ------------------------------------------------------
 *
 * Verify the quantization error for digital systems in closed-loop.
 *
 * This property analyses the plant and the controller performance
 * when connected using SERIES or FEEDBACK. The verification engine
 * checks whether the digital controllers' FWL effects causes an unexpected
 * error bound
 *
 * The engine consider nondet inputs and nondet zeroes states
 * for the desired realization (DFI, DFII, and TDFII).
 *
 * ------------------------------------------------------
 */
#ifndef DSVERIFIER_ENGINE_VERIFY_ERROR_CLOSEDLOOP_H
#define DSVERIFIER_ENGINE_VERIFY_ERROR_CLOSEDLOOP_H

extern digital_system plant;
extern digital_system plant_cbmc;
extern digital_system controller;

int verify_error_closedloop(void)
{
  set_overflow_mode = WRAPAROUND;

  /* generating closed loop for series or feedback */
  double * c_num = controller.b;
  int c_num_size = controller.b_size;
  double * c_den = controller.a;
  int c_den_size = controller.a_size;

  /* quantizing controller coefficients */
  fxp_t c_num_fxp[controller.b_size];

  fxp_double_to_fxp_array(c_num, c_num_fxp, controller.b_size);

  fxp_t c_den_fxp[controller.a_size];

  fxp_double_to_fxp_array(c_den, c_den_fxp, controller.a_size);

  /* getting quantized controller coefficients */
  double c_num_qtz[controller.b_size];

  fxp_to_double_array(c_num_qtz, c_num_fxp, controller.b_size);

  double c_den_qtz[controller.a_size];

  fxp_to_double_array(c_den_qtz, c_den_fxp, controller.a_size);

  /* getting plant coefficients */

#if (BMC == ESBMC)
  double * p_num = plant.b;
  int p_num_size = plant.b_size;
  double * p_den = plant.a;
  int p_den_size = plant.a_size;
#elif (BMC == CBMC)
  double * p_num = plant_cbmc.b;
  int p_num_size = plant.b_size;
  double * p_den = plant_cbmc.a;
  int p_den_size = plant.a_size;
#endif

  double ans_num_double[100];
  double ans_num_qtz[100];
  int ans_num_size = controller.b_size + plant.b_size - 1;
  double ans_den_qtz[100];
  double ans_den_double[100];
  int ans_den_size = controller.a_size + plant.a_size - 1;

#if (CONNECTION_MODE == SERIES)
  ft_closedloop_series(c_num_qtz, c_num_size, c_den_qtz, c_den_size, p_num,
      p_num_size, p_den, p_den_size, ans_num_qtz, ans_num_size, ans_den_qtz,
      ans_den_size);
  ft_closedloop_series(c_num, c_num_size, c_den, c_den_size, p_num, p_num_size,
      p_den, p_den_size, ans_num_double, ans_num_size, ans_den_double,
      ans_den_size);
#elif (CONNECTION_MODE == FEEDBACK)
  ft_closedloop_feedback(c_num_qtz,
      c_num_size,
      c_den_qtz,
      c_den_size,
      p_num,
      p_num_size,
      p_den,
      p_den_size,
      ans_num_qtz,
      ans_num_size,
      ans_den_qtz,
      ans_den_size);
  ft_closedloop_feedback(c_num,
      c_num_size,
      c_den,
      c_den_size,
      p_num,
      p_num_size,
      p_den,
      p_den_size,
      ans_num_double,
      ans_num_size,
      ans_den_double,
      ans_den_size);
#endif

  int i;
  double y_qtz[X_SIZE_VALUE];
  double y_double[X_SIZE_VALUE];
  double x_qtz[X_SIZE_VALUE];
  double x_double[X_SIZE_VALUE];
  double xaux_qtz[ans_num_size];
  double xaux_double[ans_num_size];

  /* prepare inputs (all possibles values in dynamical range) */
  double xaux[ans_num_size];
  double nondet_constant_input = nondet_double();

  __DSVERIFIER_assume(
      (nondet_constant_input >= impl.min)
          && (nondet_constant_input <= impl.max));

  for(i = 0; i < X_SIZE_VALUE; ++i)
  {
    x_qtz[i] = nondet_constant_input;
    x_double[i] = nondet_constant_input;
    y_qtz[i] = 0;
    y_double[i] = 0;
  }

  for(i = 0; i < ans_num_size; ++i)
  {
    xaux_qtz[i] = nondet_constant_input;
    xaux_double[i] = nondet_constant_input;
  }

  double yaux_qtz[ans_den_size];
  double yaux_double[ans_den_size];
  double y0_qtz[ans_den_size];
  double y0_double[ans_den_size];
  int Nw = (ans_den_size > ans_num_size) ? ans_den_size : ans_num_size;
  double waux_qtz[Nw];
  double waux_double[Nw];
  double w0_qtz[Nw];
  double w0_double[Nw];

#if (REALIZATION == DFI)
  for(i = 0; i < ans_den_size; ++i)
  {
    yaux_qtz[i] = 0;
    yaux_double[i] = 0;
  }
#else
  for (i = 0; i < Nw; ++i)
  {
    waux_qtz[i] = 0;
    waux_double[i] = 0;
  }
#endif

  for(i = 0; i < X_SIZE_VALUE; ++i)
  {
    /* direct form I realization */

#if (REALIZATION == DFI)

    /* realization with controller quantized */
    shiftLDouble(x_qtz[i], xaux_qtz, ans_num_size);

    y_qtz[i] = double_direct_form_1(yaux_qtz, xaux_qtz, ans_den_qtz,
        ans_num_qtz, ans_den_size, ans_num_size);

    shiftLDouble(y_qtz[i], yaux_qtz, ans_den_size);

    /* realization with controller non quantized */
    shiftLDouble(x_double[i], xaux_double, ans_num_size);

    y_double[i] = double_direct_form_1(yaux_double, xaux_double, ans_den_double,
        ans_num_double, ans_den_size, ans_num_size);

    shiftLDouble(y_double[i], yaux_double, ans_den_size);
#endif

    /* direct form II realization */

#if (REALIZATION == DFII)

    /* realization with controller quantized */
    shiftRDdouble(0, waux_qtz, Nw);

    y_qtz[i] = double_direct_form_2(waux_qtz, x_qtz[i], ans_den_qtz,
        ans_num_qtz, ans_den_size, ans_num_size);

    /* realization with controller non quantized */
    shiftRDdouble(0, waux_double, Nw);

    y_double[i] = double_direct_form_2(waux_double, x_double[i], ans_den_double,
        ans_num_double, ans_den_size, ans_num_size);
#endif

    /* transposed direct form II realization */

#if (REALIZATION == TDFII)

    /* realization with controller quantized */
    y_qtz[i] = double_transposed_direct_form_2(waux_qtz, x_qtz[i], ans_den_qtz,
        ans_num_qtz, ans_den_size, ans_num_size);

    /* realization with controller non quantized */
    y_double[i] = double_transposed_direct_form_2(waux_double, x_double[i],
        ans_den_double, ans_num_double, ans_den_size, ans_num_size);
#endif

    /* absolute error = actual value (double) - measured value (fxp) */
    double absolute_error = y_double[i] - fxp_to_double(y_qtz[i]);

    /* error verification defined by the user */
    __DSVERIFIER_assert(
        (absolute_error < (impl.max_error))
            && (absolute_error > (-impl.max_error)));
  }

  return 0;
}
#endif //DSVERIFIER_ENGINE_VERIFY_ERROR_CLOSEDLOOP_H
