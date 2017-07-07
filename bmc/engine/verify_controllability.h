/**
 * # DSVerifier - Digital Systems Verifier (Controllability)
 * #
 * #                Universidade Federal do Amazonas - UFAM
 * #
 * # Authors:       Iury Bessa     <iury.bessa@gmail.com>
 * #                Hussama Ismail <hussamaismail@gmail.com>
 * #                Felipe Monteiro <felipemonteiro@ufam.edu.br>
 * # ------------------------------------------------------
 * #
 * # ------------------------------------------------------
 */
extern digital_system_state_space _controller;

int verify_controllability(void)
{
  // setting up variables
  int i;
  int j;
  fxp_t A_fpx[LIMIT][LIMIT];
  fxp_t B_fpx[LIMIT][LIMIT];
  fxp_t controllabilityMatrix[LIMIT][LIMIT];
  fxp_t backup[LIMIT][LIMIT];
  fxp_t backupSecond[LIMIT][LIMIT];
  double controllabilityMatrix_double[LIMIT][LIMIT];

  // initializing variables
  for(i = 0; i < nStates; i++)
  {
    for(j = 0; j < (nStates * nInputs); j++)
    {
      A_fpx[i][j] = 0.0;
      B_fpx[i][j] = 0.0;
      controllabilityMatrix[i][j] = 0.0;
      backup[i][j] = 0.0;
      backupSecond[i][j] = 0.0;
      controllabilityMatrix_double[i][j] = 0.0;
    }
  }

  // converting A and B matrix to fixed point
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

  if(nInputs > 1)
  {    // checking if it is a MIMO system
    int l = 0;

    // calculating controllability matrix from the MIMO system
    for(j = 0; j < (nStates * nInputs);)
    {
      fxp_exp_matrix(nStates, nStates, A_fpx, l, backup);
      l++;
      fxp_matrix_multiplication(nStates, nStates, nStates, nInputs, backup,
          B_fpx, backupSecond);

      for(int k = 0; k < nInputs; k++)
      {
        for(i = 0; i < nStates; i++)
        {
          controllabilityMatrix[i][j] = backupSecond[i][k];
        }

        j++;
      }
    }

    for(i = 0; i < nStates; i++)
    {
      for(j = 0; j < (nStates * nInputs); j++)
      {
        backup[i][j] = 0.0;
      }
    }

    // Calculating transpose matrix
    fxp_transpose(controllabilityMatrix, backup, nStates, (nStates * nInputs));

    // Calculating C*C'
    fxp_t mimo_controllabilityMatrix_fxp[LIMIT][LIMIT];

    fxp_matrix_multiplication(nStates, (nStates * nInputs), (nStates * nInputs),
        nStates, controllabilityMatrix, backup, mimo_controllabilityMatrix_fxp);

    // Converting controllability matrix from fixed point to double
    for(i = 0; i < nStates; i++)
    {
      for(j = 0; j < nStates; j++)
      {
        controllabilityMatrix_double[i][j] = fxp_to_double(
            mimo_controllabilityMatrix_fxp[i][j]);
      }
    }

    // Calculating determinant
    // assert(fxp_determinant(mimo_controllabilityMatrix_fxp,nStates) != 0);
    assert(determinant(controllabilityMatrix_double, nStates) != 0);
  }
  else
  {
    // Checking a SISO system
    // Calculating controllability matrix
    for(j = 0; j < nStates; j++)
    {
      fxp_exp_matrix(nStates, nStates, A_fpx, j, backup);
      fxp_matrix_multiplication(nStates, nStates, nStates, nInputs, backup,
          B_fpx, backupSecond);

      for(i = 0; i < nStates; i++)
      {
        controllabilityMatrix[i][j] = backupSecond[i][0];
      }
    }

    // Converting controllability matrix from fixed point to double
    for(i = 0; i < nStates; i++)
    {
      for(j = 0; j < nStates; j++)
      {
        controllabilityMatrix_double[i][j] = fxp_to_double(
            controllabilityMatrix[i][j]);
      }
    }

    // Calculating determinant
    assert(determinant(controllabilityMatrix_double, nStates) != 0);
  }

  return 0;
}

// This version performs all operations using only double values
int verify_controllability_double(void)
{
  int i;
  int j;
  double controllabilityMatrix[LIMIT][LIMIT];
  double backup[LIMIT][LIMIT];
  double backupSecond[LIMIT][LIMIT];
  double controllabilityMatrix_double[LIMIT][LIMIT];

  if(nInputs > 1)
  {
    int l = 0;

    for(j = 0; j < (nStates * nInputs);)
    {
      double_exp_matrix(nStates, nStates, _controller.A, l, backup);
      l++;
      double_matrix_multiplication(nStates, nStates, nStates, nInputs, backup,
          _controller.B, backupSecond);

      for(int k = 0; k < nInputs; k++)
      {
        for(i = 0; i < nStates; i++)
        {
          controllabilityMatrix[i][j] = backupSecond[i][k];
        }

        j++;
      }
    }

    for(i = 0; i < nStates; i++)
    {
      for(j = 0; j < (nStates * nInputs); j++)
      {
        backup[i][j] = 0.0;
      }
    }

    transpose(controllabilityMatrix, backup, nStates, (nStates * nInputs));

    double mimo_controllabilityMatrix_double[LIMIT][LIMIT];

    double_matrix_multiplication(nStates, (nStates * nInputs),
        (nStates * nInputs), nStates, controllabilityMatrix, backup,
        mimo_controllabilityMatrix_double);
    assert(determinant(mimo_controllabilityMatrix_double, nStates) != 0);
  }
  else
  {
    for(j = 0; j < nStates; j++)
    {
      double_exp_matrix(nStates, nStates, _controller.A, j, backup);
      double_matrix_multiplication(nStates, nStates, nStates, nInputs, backup,
          _controller.B, backupSecond);

      for(i = 0; i < nStates; i++)
      {
        controllabilityMatrix[i][j] = backupSecond[i][0];
      }
    }

    assert(determinant(controllabilityMatrix, nStates) != 0);
  }

  return 0;
}
