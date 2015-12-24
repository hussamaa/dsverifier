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
# ------------------------------------------------------
*/

extern digital_system_state_space _controller;

int verify_controllability(void){
	OVERFLOW_MODE = 0;
	int i;
	int j;

	fxp_t A_fpx[LIMIT][LIMIT];
	fxp_t B_fpx[LIMIT][LIMIT];
    fxp_t controllabilityMatrix[LIMIT][LIMIT];
    fxp_t backup[LIMIT][LIMIT];
    fxp_t backupSecond[LIMIT][LIMIT];
	double controllabilityMatrix_double[LIMIT][LIMIT];

	for(i=0; i<nStates;i++){
		for(j=0; j<nStates;j++){
			controllabilityMatrix[i][j]= 0;
			A_fpx[i][j]=0;
			B_fpx[i][j]= 0;
			backup[i][j]= 0;
			backupSecond[i][j]= 0;
		}
	}

	for(i=0; i<nStates;i++){
		for(j=0; j<nStates;j++){
			A_fpx[i][j]= fxp_double_to_fxp(_controller.A[i][j]);
		}
	}

	for(i=0; i<nStates;i++){
		for(j=0; j<nInputs;j++){
			B_fpx[i][j]= fxp_double_to_fxp(_controller.B[i][j]);
		}
	}

	if(nInputs > 1){
		for(j=0; j<(nStates*nInputs);){
			fxp_exp_matrix(nStates,nStates,A_fpx,j,backup);
			fxp_matrix_multiplication(nStates,nStates,nStates,nInputs,backup,B_fpx,backupSecond);
			for(int k = 0; k < nInputs; k++){
				for(i = 0; i<nStates;i++){
						controllabilityMatrix[i][j]= backupSecond[i][0];
				}
				j++;
			}
		}
	} else {
		for(j=0; j<nStates;j++){
			fxp_exp_matrix(nStates,nStates,A_fpx,j,backup);
			fxp_matrix_multiplication(nStates,nStates,nStates,nInputs,backup,B_fpx,backupSecond);
			for(i = 0; i<nStates;i++){
					controllabilityMatrix[i][j]= backupSecond[i][0];
			}
		}
	}



	for(i=0; i<nStates;i++){
		for(j=0; j<nStates;j++){
			controllabilityMatrix_double[i][j]= fxp_to_double(controllabilityMatrix[i][j]);
		}
	}

	assert(determinant(controllabilityMatrix_double,nStates) != 0);

	return 0;
}
