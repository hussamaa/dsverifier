/**
# DSVerifier - Digital Systems Verifier (Limit Cycle)
#
#                Universidade Federal do Amazonas - UFAM
#
# Authors:       Renato Abreu   <renatobabreu@yahoo.com.br>
#		 Iury Bessa     <iury.bessa@gmail.com>
#                Hussama Ismail <hussamaismail@gmail.com>
# ------------------------------------------------------
#
# Main Class
#
# ------------------------------------------------------
*/

#include "verify_overflow.h"
#include "verify_limitcycle.h"
#include "verify_timing.h"
#include "verify_stability.h"
#include "verify_minphase.h"
#include <assert.h>

#ifndef _DSVERIFIER_H

	#define _DSVERIFIER_H				1

	#ifdef __cplusplus
		extern "C" {
		}
	#endif

	extern digital_system ds;
	extern implementation impl;

	void init();
	void validate();
	void call_verification_task(void * verification_task);
	float nondet_float();
	double nondet_double();

	int main(){

		init();
		validate();

		if (PROPERTY == OVERFLOW){
			call_verification_task(&verify_overflow);
		}
		if (PROPERTY == LIMIT_CYCLE){
			call_verification_task(&verify_limitcycle);
		}
		if (PROPERTY == TIMING){
			call_verification_task(&verify_timing);
		}
		if (PROPERTY == ERROR){
			call_verification_task(&verify_error);
		}
		if (PROPERTY == STABILITY){
			call_verification_task(&verify_stability);
		}
		if (PROPERTY == MINIMUM_PHASE){
			call_verification_task(&verify_minphase);
		}

		return 0;
	}

	/**
	 * Method to set the necessary parameters
	 * to DSVerifier FXP library.
	 */
	void init(){
		if (impl.frac_bits >= FXP_WIDTH){
			printf("impl.frac_bits must be less than word width!\n");
		}
		if (impl.int_bits >= FXP_WIDTH - impl.frac_bits){
		   printf("impl.int_bits must be less than word width subtracted by precision!\n");
		   assert(0);
		}
		if(impl.frac_bits >= 31){
			_fxp_one = 0x7fffffff;
		}else{
			_fxp_one = (0x00000001 << impl.frac_bits);
		}
		_fxp_half    =   (0x00000001 << (impl.frac_bits - 1));
		_fxp_minus_one    =   -(0x00000001 << impl.frac_bits);
		_fxp_min     =   -(0x00000001 << (impl.frac_bits + impl.int_bits - 1));
		_fxp_max     =   (0x00000001 << (impl.frac_bits + impl.int_bits - 1)) - 1;
		_fxp_fmask = ((((int32_t) 1) << impl.frac_bits) - 1);
		_fxp_imask = ((0x80000000) >> (FXP_WIDTH - impl.frac_bits - 1));

		int i = 0;
		/* applying scale in numerator coefficients */
		if ((impl.scale == 0) || (impl.scale == 1)){
			impl.scale = 1;
			return;
		}

		if (PROPERTY != STABILITY_CLOSED_LOOP){
			if (ds.b_size > 0){
				for(i = 0; i < ds.b_size; i++)
					ds.b[i] = ds.b[i] / impl.scale;
			}
		}else{
			if (control.b_size > 0){
				for(i = 0; i < control.b_size; i++)
					control.b[i] = control.b[i] / impl.scale;
			}
		}
	}

	/**
	 * Validate the required parameters
	 * to use DSVerifier and your properties
	 * verification.
	 */
	void validate(){
		if (impl.frac_bits > 16){
			printf("\n\n*************************************************************************************\n");
			printf("* Sorry, Processors with precision > 16 bits doesn't is supported by DSVerifier yet *\n");
			printf("*************************************************************************************\n");
			assert(0);
		}
		if (ds.a_size == 0 || ds.b_size == 0){
			printf("\n\n****************************************************************************\n");
			printf("* It is necessary to set (ds and impl) parameters to check with DSVerifier *\n");
			printf("****************************************************************************\n");
			assert(0);
		}		
		if (PROPERTY == 0){
			printf("\n\n***************************************************************************************\n");
			printf("* It is necessary to set the property to check with DSVerifier (use: -DPROPERTY=NAME) *\n");
			printf("***************************************************************************************\n");
			assert(0);
		}
		if ((PROPERTY == OVERFLOW) || (PROPERTY == LIMIT_CYCLE)){
			if (X_SIZE == 0){
				printf("\n\n********************************************************************************************\n");
				printf("* It is necessary to set a X_SIZE to use this property in DSVerifier (use: -DX_SIZE=VALUE) *\n");
				printf("********************************************************************************************\n");
				assert(0);
			}else{
				X_SIZE_VALUE = X_SIZE;
			}
		}
		if (REALIZATION == 0){
			printf("\n\n*********************************************************************************************\n");
			printf("* It is necessary to set the realization to check with DSVerifier (use: -DREALIZATION=NAME) *\n");
			printf("*********************************************************************************************\n");
			assert(0);
		}		
	}

	/**
	 * Method to call the verification task
	 * considering or not the uncertainty for
	 * digital system (ds struct)
	 */
	void call_verification_task(void * verification_task){
		((void(*)())verification_task)(); 
	}

#endif
