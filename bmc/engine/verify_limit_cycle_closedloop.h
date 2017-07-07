/**
 * DSVerifier - Digital Systems Verifier (Limit Cycle in Closed-loop)
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *
 * ------------------------------------------------------
 *
 * Verify the limit cycle oscilations for digital systems in closed-loop.
 *
 * This property analyse the plant and controller performance
 * when connected using SERIES or FEEDBACK. The verification
 * check if the digital controllers' FWL effects causes limit cycle
 * oscillations in outputs.
 *
 * The engine consider nondet inputs and nondet initial states
 * for the desired realization (DFI, DFII, and TDFII).
 *
 * ------------------------------------------------------
 */
#ifndef DSVERIFIER_ENGINE_LIMIT_CYCLE_CLOSEDLOOP_H
#define DSVERIFIER_ENGINE_LIMIT_CYCLE_CLOSEDLOOP_H

extern digital_system plant;
extern digital_system plant_cbmc;
extern digital_system controller;

double nondet_double();

int verify_limit_cycle_closed_loop(void)
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

  double ans_num[100];
  int ans_num_size = controller.b_size + plant.b_size - 1;
  double ans_den[100];
  int ans_den_size = controller.a_size + plant.a_size - 1;

#if (CONNECTION_MODE == SERIES)
  ft_closedloop_series(c_num_qtz, c_num_size, c_den_qtz, c_den_size, p_num,
      p_num_size, p_den, p_den_size, ans_num, ans_num_size, ans_den,
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
      ans_num,
      ans_num_size,
      ans_den,
      ans_den_size);
#endif

  int i;
  double y[X_SIZE_VALUE];
  double x[X_SIZE_VALUE];

  /* prepare inputs (all possibles values in dynamical range) */
  double xaux[ans_num_size];
  double nondet_constant_input = nondet_double();

  __DSVERIFIER_assume(
      (nondet_constant_input >= impl.min)
          && (nondet_constant_input <= impl.max));

  for(i = 0; i < X_SIZE_VALUE; ++i)
  {
    x[i] = nondet_constant_input;
    y[i] = 0;
  }

  for(i = 0; i < ans_num_size; ++i)
  {
    xaux[i] = nondet_constant_input;
  }

  double yaux[ans_den_size];
  double y0[ans_den_size];
  int Nw = (ans_den_size > ans_num_size) ? ans_den_size : ans_num_size;
  double waux[Nw];
  double w0[Nw];

#if (REALIZATION == DFI)
  for(i = 0; i < ans_den_size; ++i)
  {
    yaux[i] = nondet_int();

    __DSVERIFIER_assume((yaux[i] >= impl.min) && (yaux[i] <= impl.max));

    y0[i] = yaux[i];
  }
#else
  for (i = 0; i < Nw; ++i)
  {
    waux[i] = nondet_int();

    __DSVERIFIER_assume((waux[i] >= impl.min) && (waux[i] <= impl.max));

    w0[i] = waux[i];
  }
#endif

  double xk, temp;
  double * aptr, *bptr, *xptr, *yptr, *wptr;
  int j;

  for(i = 0; i < X_SIZE_VALUE; ++i)
  {
    /* direct form I realization */

#if (REALIZATION == DFI)
    shiftLDouble(x[i], xaux, ans_num_size);

    y[i] = double_direct_form_1(yaux, xaux, ans_den, ans_num, ans_den_size,
        ans_num_size);

    shiftLDouble(y[i], yaux, ans_den_size);
#endif

    /* direct form II realization */

#if (REALIZATION == DFII)
    shiftRDdouble(0, waux, Nw);

    y[i] = double_direct_form_2(waux, x[i], ans_den, ans_num, ans_den_size,
        ans_num_size);
#endif

    /* transposed direct form II realization */

#if (REALIZATION == TDFII)
    y[i] = double_transposed_direct_form_2(waux, x[i], ans_den, ans_num,
        ans_den_size, ans_num_size);
#endif

  }

  /* check oscillations in produced output */
  double_check_persistent_limit_cycle(y, X_SIZE_VALUE);

  return 0;
}
#endif //DSVERIFIER_ENGINE_LIMIT_CYCLE_CLOSEDLOOP_H
