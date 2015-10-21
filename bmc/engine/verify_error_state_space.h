/**
# DSVerifier - Digital Systems Verifier (Error)
#
#                Universidade Federal do Amazonas - UFAM
#
# Authors:       Iury Bessa     <iury.bessa@gmail.com>
#                Hussama Ismail <hussamaismail@gmail.com>
#                Felipe Monteiro <felipemonteiro@ufam.edu.br>
# ------------------------------------------------------
#
# For UNCERTAINTY: For use uncertainty, It's only permitted
# to use DFI, DFII and TDFII forms.
#
# ------------------------------------------------------
*/

extern digital_system_state_space _controller;
extern double error_limit;

int verify_error_state_space(void){
	OVERFLOW_MODE = 0;
	digital_system_state_space __backupController;
	int i;
	int j;

	for(i=0; i<rowA;i++){
		for(j=0; j<columnA;j++){
			__backupController.A[i][j]= (_controller.A[i][j]);
		}
	}

	for(i=0; i<rowB;i++){
		for(j=0; j<columnB;j++){
			__backupController.B[i][j]= (_controller.B[i][j]);
		}
	}

	for(i=0; i<rowC;i++){
		for(j=0; j<columnC;j++){
			__backupController.C[i][j]= (_controller.C[i][j]);
		}
	}

	for(i=0; i<rowD;i++){
		for(j=0; j<columnD;j++){
			__backupController.D[i][j]= (_controller.D[i][j]);
		}
	}

	for(i=0; i<rowStates;i++){
		for(j=0; j<columnStates;j++){
			__backupController.states[i][j]= (_controller.states[i][j]);
		}
	}

	for(i=0; i<rowInputs;i++){
		for(j=0; j<columnInputs;j++){
			__backupController.inputs[i][j]= (_controller.inputs[i][j]);
		}
	}

	for(i=0; i<rowOutputs;i++){
		for(j=0; j<columnOutputs;j++){
			__backupController.outputs[i][j]= (_controller.outputs[i][j]);
		}
	}

	double __quant_error = 0.0;

	double output_double = double_state_space_representation();

	for(i=0; i<rowA;i++){
		for(j=0; j<columnA;j++){
			_controller.A[i][j] = __backupController.A[i][j];
		}
	}

	for(i=0; i<rowB;i++){
		for(j=0; j<columnB;j++){
			_controller.B[i][j] = __backupController.B[i][j];
		}
	}

	for(i=0; i<rowC;i++){
		for(j=0; j<columnC;j++){
			_controller.C[i][j] = __backupController.C[i][j];
		}
	}

	for(i=0; i<rowD;i++){
		for(j=0; j<columnD;j++){
			_controller.D[i][j] = __backupController.D[i][j];
		}
	}

	for(i=0; i<rowStates;i++){
		for(j=0; j<columnStates;j++){
			_controller.states[i][j] = __backupController.states[i][j];
		}
	}

	for(i=0; i<rowInputs;i++){
		for(j=0; j<columnInputs;j++){
			_controller.inputs[i][j] = __backupController.inputs[i][j];
		}
	}

	for(i=0; i<rowOutputs;i++){
		for(j=0; j<columnOutputs;j++){
			_controller.outputs[i][j] = __backupController.outputs[i][j];
		}
	}

	double output_fxp = fxp_state_space_representation();

	__quant_error = (((output_fxp - output_double)/output_double)) * 100;

	assert(__quant_error < error_limit);

	return 0;
}
