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

extern digital_system_state_space _controller;

int verify_observability(void){

	int i;
	int j;

	fxp_t A_fpx[LIMIT][LIMIT];
	fxp_t C_fpx[LIMIT][LIMIT];
    fxp_t observabilityMatrix[LIMIT][LIMIT];
    fxp_t backup[LIMIT][LIMIT];
    fxp_t backupSecond[LIMIT][LIMIT];
	double observabilityMatrix_double[LIMIT][LIMIT];

	for(i=0; i<nStates;i++){
		for(j=0; j<nStates;j++){
			observabilityMatrix[i][j]= 0;
			A_fpx[i][j]=0;
			C_fpx[i][j]= 0;
			backup[i][j]= 0;
			backupSecond[i][j]= 0;
		}
	}

	for(i=0; i<nStates;i++){
		for(j=0; j<nStates;j++){
			A_fpx[i][j]= fxp_double_to_fxp(_controller.A[i][j]);
		}
	}

	for(i=0; i<nOutputs;i++){
		for(j=0; j<nStates;j++){
			C_fpx[i][j]= fxp_double_to_fxp(_controller.C[i][j]);
		}
	}

	for(i=0; i<nStates;i++){
		fxp_exp_matrix(nStates,nStates,A_fpx,i,backup);
		fxp_matrix_multiplication(nOutputs,nStates,nStates,nStates,C_fpx,backup,backupSecond);
		for(j = 0; j<nStates;j++){
				observabilityMatrix[i][j]= backupSecond[0][j];
		}
	}

	for(i=0; i<nStates;i++){
		for(j=0; j<nStates;j++){
			observabilityMatrix_double[i][j]= fxp_to_double(observabilityMatrix[i][j]);
		}
	}

	assert(determinant(observabilityMatrix_double,nStates) != 0);

	return 0;
}
