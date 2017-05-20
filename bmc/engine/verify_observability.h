/**
 # DSVerifier - Digital Systems Verifier (Observability)
 #
 #                Universidade Federal do Amazonas - UFAM
 #
 # Authors:       Iury Bessa     <iury.bessa@gmail.com>
 #                Hussama Ismail <hussamaismail@gmail.com>
 #                Felipe Monteiro <felipemonteiro@ufam.edu.br>
 # ------------------------------------------------------
 #
 # ------------------------------------------------------
 */

//#include <stdio.h>
//#include <stdlib.h>
extern digital_system_state_space _controller;

int verify_observability(void)
{

	//setting up variables
	int i;
	int j;

	fxp_t A_fpx[LIMIT][LIMIT];
	fxp_t C_fpx[LIMIT][LIMIT];
	fxp_t observabilityMatrix[LIMIT][LIMIT];
	fxp_t backup[LIMIT][LIMIT];
	fxp_t backupSecond[LIMIT][LIMIT];
	double observabilityMatrix_double[LIMIT][LIMIT];

	//initializing variables
	for (i = 0; i < nStates; i++)
	{
		for (j = 0; j < nStates; j++)
		{
			observabilityMatrix[i][j] = 0;
			A_fpx[i][j] = 0;
			C_fpx[i][j] = 0;
			backup[i][j] = 0;
			backupSecond[i][j] = 0;
		}
	}

	//converting A and C matrix to fixed point
	for (i = 0; i < nStates; i++)
	{
		for (j = 0; j < nStates; j++)
		{
			A_fpx[i][j] = fxp_double_to_fxp(_controller.A[i][j]);
		}
	}

	for (i = 0; i < nOutputs; i++)
	{
		for (j = 0; j < nStates; j++)
		{
			C_fpx[i][j] = fxp_double_to_fxp(_controller.C[i][j]);
		}
	}

	if (nOutputs > 1)
	{ // checking if it is a MIMO system
		int l;
		j = 0;
		for (l = 0; l < nStates;)
		{ //calculating observability matrix from the MIMO system
			fxp_exp_matrix(nStates, nStates, A_fpx, l, backup);
			l++;
			fxp_matrix_multiplication(nOutputs, nStates, nStates, nStates,
					C_fpx, backup, backupSecond);
			for (int k = 0; k < nOutputs; k++)
			{
				for (i = 0; i < nStates; i++)
				{
					observabilityMatrix[j][i] = backupSecond[k][i];
				}
				j++;
			}
		}
		/*
		 for(i=0; i<(nStates*nOutputs);i++){
		 for(j=0; j<nStates;j++){
		 observabilityMatrix_double[i][j]= fxp_to_double(observabilityMatrix[i][j]);
		 }
		 }

		 printf("#matrix: OBSERVABILITY MATRIX:\n\n");
		 print_matrix(observabilityMatrix_double,(nStates*nOutputs),nStates);
		 */
		for (i = 0; i < nStates; i++)
		{
			for (j = 0; j < (nStates * nOutputs); j++)
			{
				backup[i][j] = 0.0;
			}
		}

		//Calculating transpose matrix
		fxp_transpose(observabilityMatrix, backup, (nStates * nOutputs),
				nStates);
		/*
		 for(i=0; i<nStates;i++){
		 for(j=0; j<(nStates*nOutputs);j++){
		 observabilityMatrix_double[i][j]= fxp_to_double(backup[i][j]);
		 }
		 }

		 printf("#matrix: TRANSPOSE OBSERVABILITY MATRIX:\n\n");
		 print_matrix(observabilityMatrix_double,nStates,(nStates*nOutputs));
		 */
		//Calculating O'*O
		fxp_t mimo_observabilityMatrix_fxp[LIMIT][LIMIT];
		fxp_matrix_multiplication(nStates, (nStates * nOutputs),
				(nStates * nOutputs), nStates, backup, observabilityMatrix,
				mimo_observabilityMatrix_fxp);
		/*
		 for(i=0; i<nStates;i++){
		 for(j=0; j<nStates;j++){
		 observabilityMatrix_double[i][j]= fxp_to_double(mimo_observabilityMatrix_fxp[i][j]);
		 }
		 }

		 printf("#matrix: FINAL MATRIX:\n\n");
		 print_matrix(observabilityMatrix_double,nStates,nStates);
		 */
		//Converting controllability matrix from fixed point to double
		for (i = 0; i < nStates; i++)
		{
			for (j = 0; j < nStates; j++)
			{
				observabilityMatrix_double[i][j] = fxp_to_double(
						mimo_observabilityMatrix_fxp[i][j]);
			}
		}

		//Calculating determinant
		assert(determinant(observabilityMatrix_double, nStates) != 0);
	}
	else
	{
		for (i = 0; i < nStates; i++)
		{
			fxp_exp_matrix(nStates, nStates, A_fpx, i, backup);
			fxp_matrix_multiplication(nOutputs, nStates, nStates, nStates,
					C_fpx, backup, backupSecond);
			for (j = 0; j < nStates; j++)
			{
				observabilityMatrix[i][j] = backupSecond[0][j];
			}
		}

		for (i = 0; i < nStates; i++)
		{
			for (j = 0; j < nStates; j++)
			{
				observabilityMatrix_double[i][j] = fxp_to_double(
						observabilityMatrix[i][j]);
			}
		}
		assert(determinant(observabilityMatrix_double, nStates) != 0);
	}

	return 0;
}
