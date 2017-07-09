/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *                Iury Bessa     <iury.bessa@gmail.com>
 *                Felipe Monteiro <felipemonteiro@ufam.edu.br>
 *
 * Contributors: Lennon Chaves <lennon.correach@gmail.com>
 *
 * ------------------------------------------------------
 *
 * Space state representation for DSVerifier
 *
 * ------------------------------------------------------
 */
#ifndef DSVERIFIER_CORE_STATE_SPACE_H
#define DSVERIFIER_CORE_STATE_SPACE_H

extern digital_system_state_space _controller;
extern int nStates;
extern int nInputs;
extern int nOutputs;

double double_state_space_representation(void)
{
  double result1[LIMIT][LIMIT];
  double result2[LIMIT][LIMIT];
  int i, j;

  for(i = 0; i < LIMIT; i++)
  {
    for(j = 0; j < LIMIT; j++)
    {
      result1[i][j] = 0;
      result2[i][j] = 0;
    }
  }

  double_matrix_multiplication(nOutputs, nStates, nStates, 1, _controller.C,
      _controller.states, result1);
  double_matrix_multiplication(nOutputs, nInputs, nInputs, 1, _controller.D,
      _controller.inputs, result2);
  double_add_matrix(nOutputs, 1, result1, result2, _controller.outputs);
  double_matrix_multiplication(nStates, nStates, nStates, 1, _controller.A,
      _controller.states, result1);
  double_matrix_multiplication(nStates, nInputs, nInputs, 1, _controller.B,
      _controller.inputs, result2);
  double_add_matrix(nStates, 1, result1, result2, _controller.states);

  return _controller.outputs[0][0];
}

double fxp_state_space_representation(void)
{
  fxp_t result1[LIMIT][LIMIT];
  fxp_t result2[LIMIT][LIMIT];
  int i, j;

  for(i = 0; i < LIMIT; i++)
  {
    for(j = 0; j < LIMIT; j++)
    {
      result1[i][j] = 0;
      result2[i][j] = 0;
    }
  }

  fxp_t A_fpx[LIMIT][LIMIT];
  fxp_t B_fpx[LIMIT][LIMIT];
  fxp_t C_fpx[LIMIT][LIMIT];
  fxp_t D_fpx[LIMIT][LIMIT];
  fxp_t states_fpx[LIMIT][LIMIT];
  fxp_t inputs_fpx[LIMIT][LIMIT];
  fxp_t outputs_fpx[LIMIT][LIMIT];

  for(i = 0; i < LIMIT; i++)
  {
    for(j = 0; j < LIMIT; j++)
    {
      A_fpx[i][j] = 0;
    }
  }

  for(i = 0; i < LIMIT; i++)
  {
    for(j = 0; j < LIMIT; j++)
    {
      B_fpx[i][j] = 0;
    }
  }

  for(i = 0; i < LIMIT; i++)
  {
    for(j = 0; j < LIMIT; j++)
    {
      C_fpx[i][j] = 0;
    }
  }

  for(i = 0; i < LIMIT; i++)
  {
    for(j = 0; j < LIMIT; j++)
    {
      D_fpx[i][j] = 0;
    }
  }

  for(i = 0; i < LIMIT; i++)
  {
    for(j = 0; j < LIMIT; j++)
    {
      states_fpx[i][j] = 0;
    }
  }

  for(i = 0; i < LIMIT; i++)
  {
    for(j = 0; j < LIMIT; j++)
    {
      inputs_fpx[i][j] = 0;
    }
  }

  for(i = 0; i < LIMIT; i++)
  {
    for(j = 0; j < LIMIT; j++)
    {
      outputs_fpx[i][j] = 0;
    }
  }

  for(i = 0; i < nStates; i++)
  {
    for(j = 0; j < nStates; j++)
    {
      A_fpx[i][j] = fxp_double_to_fxp(_controller.A[i][j]);
    }
  }

  for(i = 0; i < nStates; i++)
  {
    for(j = 0; j < nInputs; j++)
    {
      B_fpx[i][j] = fxp_double_to_fxp(_controller.B[i][j]);
    }
  }

  for(i = 0; i < nOutputs; i++)
  {
    for(j = 0; j < nStates; j++)
    {
      C_fpx[i][j] = fxp_double_to_fxp(_controller.C[i][j]);
    }
  }

  for(i = 0; i < nOutputs; i++)
  {
    for(j = 0; j < nInputs; j++)
    {
      D_fpx[i][j] = fxp_double_to_fxp(_controller.D[i][j]);
    }
  }

  for(i = 0; i < nStates; i++)
  {
    for(j = 0; j < 1; j++)
    {
      states_fpx[i][j] = fxp_double_to_fxp(_controller.states[i][j]);
    }
  }

  for(i = 0; i < nInputs; i++)
  {
    for(j = 0; j < 1; j++)
    {
      inputs_fpx[i][j] = fxp_double_to_fxp(_controller.inputs[i][j]);
    }
  }

  for(i = 0; i < nOutputs; i++)
  {
    for(j = 0; j < 1; j++)
    {
      outputs_fpx[i][j] = fxp_double_to_fxp(_controller.outputs[i][j]);
    }
  }

  fxp_matrix_multiplication(nOutputs, nStates, nStates, 1, C_fpx, states_fpx,
      result1);
  fxp_matrix_multiplication(nOutputs, nInputs, nInputs, 1, D_fpx, inputs_fpx,
      result2);
  fxp_add_matrix(nOutputs, 1, result1, result2, outputs_fpx);
  fxp_matrix_multiplication(nStates, nStates, nStates, 1, A_fpx, states_fpx,
      result1);
  fxp_matrix_multiplication(nStates, nInputs, nInputs, 1, B_fpx, inputs_fpx,
      result2);
  fxp_add_matrix(nStates, 1, result1, result2, states_fpx);

  for(i = 0; i < nStates; i++)
  {
    for(j = 0; j < 1; j++)
    {
      _controller.states[i][j] = fxp_to_double(states_fpx[i][j]);
    }
  }

  for(i = 0; i < nOutputs; i++)
  {
    for(j = 0; j < 1; j++)
    {
      _controller.outputs[i][j] = fxp_to_double(outputs_fpx[i][j]);
    }
  }

  return _controller.outputs[0][0];
}
#endif //DSVERIFIER_CORE_STATE_SPACE_H
