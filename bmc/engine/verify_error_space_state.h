/**
# DSVerifier - Digital Systems Verifier (Error)
#
#                Universidade Federal do Amazonas - UFAM
#
# Authors:       Renato Abreu   <renatobabreu@yahoo.com.br>
#				 Iury Bessa     <iury.bessa@gmail.com>
#                Hussama Ismail <hussamaismail@gmail.com>
# ------------------------------------------------------
#
# For UNCERTAINTY: For use uncertainty, It's only permited
# to use DFI, DFII and TDFII forms.
#
# ------------------------------------------------------
*/

extern digital_system_space_state _controller;

int verify_error_space_state(void){

	space_state_representation();

	assert(_controller.states[0][0] > -70 && _controller.states[0][0] < -67);
	assert(_controller.states[1][0] > 214 && _controller.states[1][0] < 215);

	return 0;
}
