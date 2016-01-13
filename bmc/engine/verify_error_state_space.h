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

	for(i=0; i<nStates;i++){
		for(j=0; j<nStates;j++){
			__backupController.A[i][j]= (_controller.A[i][j]);
		}
	}

	for(i=0; i<nStates;i++){
		for(j=0; j<nInputs;j++){
			__backupController.B[i][j]= (_controller.B[i][j]);
		}
	}

	for(i=0; i<nOutputs;i++){
		for(j=0; j<nStates;j++){
			__backupController.C[i][j]= (_controller.C[i][j]);
		}
	}

	for(i=0; i<nOutputs;i++){
		for(j=0; j<nInputs;j++){
			__backupController.D[i][j]= (_controller.D[i][j]);
		}
	}

	for(i=0; i<nStates;i++){
		for(j=0; j<1;j++){
			__backupController.states[i][j]= (_controller.states[i][j]);
		}
	}

	for(i=0; i<nInputs;i++){
		for(j=0; j<1;j++){
			__backupController.inputs[i][j]= (_controller.inputs[i][j]);
		}
	}

	for(i=0; i<nOutputs;i++){
		for(j=0; j<1;j++){
			__backupController.outputs[i][j]= (_controller.outputs[i][j]);
		}
	}

	double __quant_error = 0.0;

	double output_double = double_state_space_representation();

	for(i=0; i<nStates;i++){
		for(j=0; j<nStates;j++){
			_controller.A[i][j] = __backupController.A[i][j];
		}
	}

	for(i=0; i<nStates;i++){
		for(j=0; j<nInputs;j++){
			_controller.B[i][j] = __backupController.B[i][j];
		}
	}

	for(i=0; i<nOutputs;i++){
		for(j=0; j<nStates;j++){
			_controller.C[i][j] = __backupController.C[i][j];
		}
	}

	for(i=0; i<nOutputs;i++){
		for(j=0; j<nInputs;j++){
			_controller.D[i][j] = __backupController.D[i][j];
		}
	}

	for(i=0; i<nStates;i++){
		for(j=0; j<1;j++){
			_controller.states[i][j] = __backupController.states[i][j];
		}
	}

	for(i=0; i<nInputs;i++){
		for(j=0; j<1;j++){
			_controller.inputs[i][j] = __backupController.inputs[i][j];
		}
	}

	for(i=0; i<nOutputs;i++){
		for(j=0; j<1;j++){
			_controller.outputs[i][j] = __backupController.outputs[i][j];
		}
	}

	double output_fxp = fxp_state_space_representation();

	fxp_verify_overflow(output_fxp);

	__quant_error = (((output_fxp - output_double)/output_double)) * 100;

	assert(__quant_error < error_limit && __quant_error > (-error_limit));

	return 0;
}
