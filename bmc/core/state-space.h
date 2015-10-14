/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *                Iury Bessa     <iury.bessa@gmail.com>
 *                Felipe Monteiro <felipemonteiro@ufam.edu.br>
 *
 * ------------------------------------------------------
 *
 * Space state representation for DSVerifier
 *
 * ------------------------------------------------------
 */

extern digital_system_state_space _controller;

extern int rowA;
extern int columnA;
extern int rowB;
extern int columnB;
extern int rowC;
extern int columnC;
extern int rowD;
extern int columnD;
extern int rowInputs;
extern int columnInputs;
extern int rowStates;
extern int columnStates;
extern int rowOutputs;
extern int columnOutputs;

double double_state_space_representation(void){

	double result1[LIMIT][LIMIT];
	double result2[LIMIT][LIMIT];

	int i, j, k;
	for(i=0; i<LIMIT;i++){
		for(j=0; j<LIMIT;j++){
			result1[i][j]=0;
			result2[i][j]=0;
		}
	}

	double_matrix_multiplication(rowC,columnC,rowStates,columnStates,_controller.C,_controller.states,result1);
	double_matrix_multiplication(rowD,columnD,rowInputs,columnInputs,_controller.D,_controller.inputs,result2);

	double_add_matrix(rowC,
			columnStates,
			result1,
			result2,
			_controller.outputs);

	for (i = 1; i < K_SIZE; i++) {
		double_matrix_multiplication(rowA,columnA,rowStates,columnStates,_controller.A,_controller.states,result1);
		double_matrix_multiplication(rowB,columnB,rowInputs,columnInputs,_controller.B,_controller.inputs,result2);

		double_add_matrix(rowA,
				columnStates,
				result1,
				result2,
				_controller.states);

		double_matrix_multiplication(rowC,columnC,rowStates,columnStates,_controller.C,_controller.states,result1);
		double_matrix_multiplication(rowD,columnD,rowInputs,columnInputs,_controller.D,_controller.inputs,result2);

		double_add_matrix(rowC,
				columnStates,
				result1,
				result2,
				_controller.outputs);
	}
	return _controller.outputs[0][0];
}

double fxp_state_space_representation(void){

	fxp32_t result1[LIMIT][LIMIT];
	fxp32_t result2[LIMIT][LIMIT];

	int i, j, k;
	for(i=0; i<LIMIT;i++){
		for(j=0; j<LIMIT;j++){
			result1[i][j]=0;
			result2[i][j]=0;
		}
	}

	fxp32_t A_fpx[LIMIT][LIMIT];
	fxp32_t B_fpx[LIMIT][LIMIT];
	fxp32_t C_fpx[LIMIT][LIMIT];
	fxp32_t D_fpx[LIMIT][LIMIT];
	fxp32_t states_fpx[LIMIT][LIMIT];
	fxp32_t inputs_fpx[LIMIT][LIMIT];
	fxp32_t outputs_fpx[LIMIT][LIMIT];

	for(i=0; i<LIMIT;i++){
		for(j=0; j<LIMIT;j++){
			A_fpx[i][j]=0;
		}
	}

	for(i=0; i<LIMIT;i++){
		for(j=0; j<LIMIT;j++){
			B_fpx[i][j]=0;
		}
	}

	for(i=0; i<LIMIT;i++){
		for(j=0; j<LIMIT;j++){
			C_fpx[i][j]=0;
		}
	}

	for(i=0; i<LIMIT;i++){
		for(j=0; j<LIMIT;j++){
			D_fpx[i][j]=0;
		}
	}

	for(i=0; i<LIMIT;i++){
		for(j=0; j<LIMIT;j++){
			states_fpx[i][j]=0;
		}
	}

	for(i=0; i<LIMIT;i++){
		for(j=0; j<LIMIT;j++){
			inputs_fpx[i][j]=0;
		}
	}

	for(i=0; i<LIMIT;i++){
		for(j=0; j<LIMIT;j++){
			outputs_fpx[i][j]=0;
		}
	}

	for(i=0; i<rowA;i++){
		for(j=0; j<columnA;j++){
			A_fpx[i][j]= fxp_double_to_fxp(_controller.A[i][j]);
		}
	}

	for(i=0; i<rowB;i++){
		for(j=0; j<columnB;j++){
			B_fpx[i][j]= fxp_double_to_fxp(_controller.B[i][j]);
		}
	}

	for(i=0; i<rowC;i++){
		for(j=0; j<columnC;j++){
			C_fpx[i][j]= fxp_double_to_fxp(_controller.C[i][j]);
		}
	}

	for(i=0; i<rowD;i++){
		for(j=0; j<columnD;j++){
			D_fpx[i][j]= fxp_double_to_fxp(_controller.D[i][j]);
		}
	}

	for(i=0; i<rowStates;i++){
		for(j=0; j<columnStates;j++){
			states_fpx[i][j]= fxp_double_to_fxp(_controller.states[i][j]);
		}
	}

	for(i=0; i<rowInputs;i++){
		for(j=0; j<columnInputs;j++){
			inputs_fpx[i][j]= fxp_double_to_fxp(_controller.inputs[i][j]);
		}
	}

	for(i=0; i<rowOutputs;i++){
		for(j=0; j<columnOutputs;j++){
			outputs_fpx[i][j]= fxp_double_to_fxp(_controller.outputs[i][j]);
		}
	}

	fxp_matrix_multiplication(rowC,columnC,rowStates,columnStates,C_fpx,states_fpx,result1);
	fxp_matrix_multiplication(rowD,columnD,rowInputs,columnInputs,D_fpx,inputs_fpx,result2);

	fxp_add_matrix(rowC,
			columnStates,
			result1,
			result2,
			outputs_fpx);

	for (i = 1; i < K_SIZE; i++) {
		fxp_matrix_multiplication(rowA,columnA,rowStates,columnStates,A_fpx,states_fpx,result1);
		fxp_matrix_multiplication(rowB,columnB,rowInputs,columnInputs,B_fpx,inputs_fpx,result2);

		fxp_add_matrix(rowA,
				columnStates,
				result1,
				result2,
				states_fpx);

		fxp_matrix_multiplication(rowC,columnC,rowStates,columnStates,C_fpx,states_fpx,result1);
		fxp_matrix_multiplication(rowD,columnD,rowInputs,columnInputs,D_fpx,inputs_fpx,result2);

		fxp_add_matrix(rowC,
				columnStates,
				result1,
				result2,
				outputs_fpx);
	}

	for(i=0; i<rowStates;i++){
		for(j=0; j<columnStates;j++){
			_controller.states[i][j]= fxp_to_double(states_fpx[i][j]);
		}
	}

	for(i=0; i<rowOutputs;i++){
		for(j=0; j<columnOutputs;j++){
			_controller.outputs[i][j]= fxp_to_double(outputs_fpx[i][j]);
		}
	}

	return _controller.outputs[0][0];
}
