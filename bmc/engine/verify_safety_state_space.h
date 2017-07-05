/**
 * # DSVerifier - Digital Systems Verifier (Error)
 * #
 * #                Universidade Federal do Amazonas - UFAM
 * #
 * # Authors:       Iury Bessa     <iury.bessa@gmail.com>
 * #                Hussama Ismail <hussamaismail@gmail.com>
 * #                Felipe Monteiro <felipemonteiro@ufam.edu.br>
 * # ------------------------------------------------------
 * #
 * # For UNCERTAINTY: For use uncertainty, It's only permitted
 * # to use DFI, DFII and TDFII forms.
 * #
 * # ------------------------------------------------------
 */
extern digital_system_state_space _controller;
extern double error_limit;
extern int closed_loop;

double fxp_ss_closed_loop_safety()
{
	double reference[LIMIT][LIMIT];
	double result1[LIMIT][LIMIT];
	double result2[LIMIT][LIMIT];
	fxp_t K_fpx[LIMIT][LIMIT];
	fxp_t outputs_fpx[LIMIT][LIMIT];
	fxp_t result_fxp[LIMIT][LIMIT];
	unsigned int i;
	unsigned int j;
	unsigned int k;
	short unsigned int flag = 0; // flag is 0 if matrix D is null matrix, otherwise flag is 1

	for (i = 0; i < nOutputs; i++)
	{    // check if matrix D is a null matrix
		for (j = 0; j < nInputs; j++)
		{
			if (_controller.D[i][j] != 0)
			{
				flag = 1;
			}
		}
	}

	for (i = 0; i < nInputs; i++)
	{
		for (j = 0; j < 1; j++)
		{
			reference[i][j] = (_controller.inputs[i][j]);
		}
	}

	for (i = 0; i < nInputs; i++)
	{
		for (j = 0; j < nOutputs; j++)
		{
			K_fpx[i][j] = 0;
		}
	}

	for (i = 0; i < nOutputs; i++)
	{
		for (j = 0; j < 1; j++)
		{
			outputs_fpx[i][j] = 0;
		}
	}

	for (i = 0; i < LIMIT; i++)
	{
		for (j = 0; j < LIMIT; j++)
		{
			result_fxp[i][j] = 0;
		}
	}

	for (i = 0; i < nInputs; i++)
	{
		for (j = 0; j < nOutputs; j++)
		{
			K_fpx[i][j] = fxp_double_to_fxp(_controller.K[i][j]);
		}
	}

	for (i = 0; i < LIMIT; i++)
	{
		for (j = 0; j < LIMIT; j++)
		{
			result1[i][j] = 0;
			result2[i][j] = 0;
		}
	}

	for (i = 1; i < K_SIZE; i++)
	{
		double_matrix_multiplication(nOutputs, nStates, nStates, 1,
				_controller.C, _controller.states, result1);

		if (flag == 1)
		{
			double_matrix_multiplication(nOutputs, nInputs, nInputs, 1,
					_controller.D, _controller.inputs, result2);
		}

		double_add_matrix(nOutputs, 1, result1, result2, _controller.outputs);

		for (k = 0; k < nOutputs; k++)
		{
			for (j = 0; j < 1; j++)
			{
				outputs_fpx[k][j] = fxp_double_to_fxp(
						_controller.outputs[k][j]);
			}
		}

		fxp_matrix_multiplication(nInputs, nOutputs, nOutputs, 1, K_fpx,
				outputs_fpx, result_fxp);

		for (k = 0; k < nInputs; k++)
		{
			for (j = 0; j < 1; j++)
			{
				result1[k][j] = fxp_to_double(result_fxp[k][j]);
			}
		}

		printf("### fxp: U (before) = %.9f", _controller.inputs[0][0]);
		printf("### fxp: reference = %.9f", reference[0][0]);
		printf("### fxp: result1 = %.9f", result1[0][0]);
		printf("### fxp: reference - result1 = %.9f",
				(reference[0][0] - result1[0][0]));
		double_sub_matrix(nInputs, 1, reference, result1, _controller.inputs);
		printf("### fxp: Y = %.9f", _controller.outputs[0][0]);
		printf("### fxp: U (after) = %.9f \n### \n### ",
				_controller.inputs[0][0]);
		double_matrix_multiplication(nStates, nStates, nStates, 1,
				_controller.A, _controller.states, result1);
		double_matrix_multiplication(nStates, nInputs, nInputs, 1,
				_controller.B, _controller.inputs, result2);
		double_add_matrix(nStates, 1, result1, result2, _controller.states);
	}

	return _controller.outputs[0][0];
}

int verify_safety_state_space(void)
{
	fxp_t output_fxp = fxp_ss_closed_loop_safety();
	double output_double = fxp_to_double(output_fxp);

	assert(output_double <= error_limit);

	return 0;
}
