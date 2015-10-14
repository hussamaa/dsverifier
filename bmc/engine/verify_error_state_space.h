/**
# DSVerifier - Digital Systems Verifier (Error)
#
#                Universidade Federal do Amazonas - UFAM
#
# Authors:       Renato Abreu   <renatobabreu@yahoo.com.br>
#				 Iury Bessa     <iury.bessa@gmail.com>
#                Hussama Ismail <hussamaismail@gmail.com>
#                Felipe Monteiro <felipemonteiro@ufam.edu.br>
# ------------------------------------------------------
#
# For UNCERTAINTY: For use uncertainty, It's only permited
# to use DFI, DFII and TDFII forms.
#
# ------------------------------------------------------
*/

extern digital_system_state_space _controller;

int verify_error_state_space(void){

	fxp_state_space_representation();

	//FOR BOUND 2
	//assert(_controller.states[0][0] > -0.5 && _controller.states[0][0] < 0.5);
	//assert(_controller.states[1][0] > 1 && _controller.states[1][0] < 2);
	//assert(_controller.outputs[0][0] > 0.85 && _controller.outputs[0][0] < 0.95);
	//FOR BOUND 3
	//assert(_controller.states[0][0] > -1.7 && _controller.states[0][0] < -1.3);
	//assert(_controller.states[1][0] > 8.8 && _controller.states[1][0] < 9.2);
	//assert(_controller.outputs[0][0] > 3.8 && _controller.outputs[0][0] < 3.95);
	//FOR BOUND 4
	//assert(_controller.states[0][0]  > -12.2 &&  _controller.states[0][0]  < -11.8);
	//assert(_controller.states[1][0]  > 44.8  &&  _controller.states[1][0]  < 45.2);
	//assert(_controller.outputs[0][0] > 14.8  &&  _controller.outputs[0][0] < 15.2);
	//FOR BOUND 5
	//assert(_controller.outputs[0][0] > 59  &&  _controller.outputs[0][0] < 60);

	return 0;
}
