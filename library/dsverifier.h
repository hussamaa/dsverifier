/**
 * DSVerifier - Digital Systems Verifier (Main)
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *                Iury Bessa     <iury.bessa@gmail.com>
 *                Renato Abreu   <renatobabreu@yahoo.com.br>
 *
 * ------------------------------------------------------
 *
 * Main Class
 *
 * ------------------------------------------------------
*/

#include "core/util.h"
#include "core/definitions.h"
#include "core/compatibility.h"
#include "core/fixed-point.h"
#include "core/functions.h"
#include "core/realizations.h"
#include "core/delta-operator.h"
#include "core/closed-loop.h"

#include "engine/verify_overflow.h"
#include "engine/verify_limit_cycle.h"
#include "engine/verify_zero_input_limit_cycle.h"
#include "engine/verify_timing.h"
#include "engine/verify_stability.h"
#include "engine/verify_minimum_phase.h"
#include "engine/verify_stability_closedloop.h"

extern digital_system ds;
extern digital_system plant;
extern digital_system control;
extern implementation impl;
extern hardware hw;

void init();
void validate();
void call_verification_task(void * verification_task);
void call_closedloop_verification_task(void * closedloop_verification_task);
float nondet_float();
double nondet_double();

int main(){

	init();
	validate();

	if (PROPERTY == OVERFLOW){
		call_verification_task(&verify_overflow);
	}
	if (PROPERTY == LIMIT_CYCLE){
		call_verification_task(&verify_limit_cycle);
	}
	if (PROPERTY == ZERO_INPUT_LIMIT_CYCLE){
		call_verification_task(&verify_zero_input_limit_cycle);
	}
	if (PROPERTY == TIMING){
		call_verification_task(&verify_timing);
	}
	if (PROPERTY == STABILITY){
		call_verification_task(&verify_stability);
	}
	if (PROPERTY == MINIMUM_PHASE){
		call_verification_task(&verify_minimum_phase);
	}
	if (PROPERTY == STABILITY_CLOSED_LOOP){
		call_closedloop_verification_task(&verify_stability_closedloop_using_dslib);		
	}

	return 0;
}

/** function to set the necessary parameters to DSVerifier FXP library */
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

	_fxp_half      = (0x00000001 << (impl.frac_bits - 1));
	_fxp_minus_one = -(0x00000001 << impl.frac_bits);
	_fxp_min       = -(0x00000001 << (impl.frac_bits + impl.int_bits - 1));
	_fxp_max       = (0x00000001 << (impl.frac_bits + impl.int_bits - 1)) - 1;
	_fxp_fmask     = ((((int32_t) 1) << impl.frac_bits) - 1);
	_fxp_imask     = ((0x80000000) >> (FXP_WIDTH - impl.frac_bits - 1));

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

/** validate the required parameters to use DSVerifier and your properties verification. */
void validate(){
	if (impl.frac_bits > 16){
		printf("\n\n*************************************************************************************\n");
		printf("* Sorry, Processors with precision > 16 bits doesn't is supported by DSVerifier yet *\n");
		printf("*************************************************************************************\n");
		__DSVERIFIER_assert(0);
	}
	if (((PROPERTY != STABILITY_CLOSED_LOOP) && (PROPERTY != LIMIT_CYCLE_CLOSED_LOOP)) && (ds.a_size == 0 || ds.b_size == 0)){
		printf("\n\n****************************************************************************\n");
		printf("* It is necessary to set (ds and impl) parameters to check with DSVerifier *\n");
		printf("****************************************************************************\n");
		__DSVERIFIER_assert(0);
	}
	if ((PROPERTY == STABILITY_CLOSED_LOOP) || (PROPERTY == LIMIT_CYCLE_CLOSED_LOOP)){
		if (control.a_size == 0 || plant.b_size == 0 || impl.int_bits == 0 ){
			printf("\n\n*****************************************************************************************************\n");
			printf("* It is necessary to set (control, plant and, impl) parameters to check CLOSED LOOP with DSVerifier *\n");
			printf("*****************************************************************************************************\n");
			__DSVERIFIER_assert(0);
		}
		if (CONNECTION_MODE == 0){
			printf("\n\n*****************************************************************************************************************\n");
			printf("* It is necessary to set a connection mode to check CLOSED LOOP with DSVerifier (use: -DCONNECTION_MODE=SERIES) *\n");
			printf("*****************************************************************************************************************\n");
			__DSVERIFIER_assert(0);
		}
	}
	if (PROPERTY == 0){
		printf("\n\n***************************************************************************************\n");
		printf("* It is necessary to set the property to check with DSVerifier (use: -DPROPERTY=NAME) *\n");
		printf("***************************************************************************************\n");
		__DSVERIFIER_assert(0);
	}
	if ((PROPERTY == OVERFLOW) || (PROPERTY == LIMIT_CYCLE) || (PROPERTY == ZERO_INPUT_LIMIT_CYCLE) || (PROPERTY == LIMIT_CYCLE_CLOSED_LOOP) || (PROPERTY == TIMING)){
		if (X_SIZE == 0){
			printf("\n\n********************************************************************************************\n");
			printf("* It is necessary to set a X_SIZE to use this property in DSVerifier (use: -DX_SIZE=VALUE) *\n");
			printf("********************************************************************************************\n");
			__DSVERIFIER_assert(0);
		}else{
			X_SIZE_VALUE = X_SIZE;
		}
	}
	if ((REALIZATION == 0) && (PROPERTY != STABILITY_CLOSED_LOOP)){
		printf("\n\n*********************************************************************************************\n");
		printf("* It is necessary to set the realization to check with DSVerifier (use: -DREALIZATION=NAME) *\n");
		printf("*********************************************************************************************\n");
		__DSVERIFIER_assert(0);
	}
	if (PROPERTY == ERROR){
		if (CONNECTION_MODE == 0){
			printf("\n\n*************************************************************************\n");
			printf("* You need to inform the maximum expected error (use: -DEXPECTED_ERROR) *\n");
			printf("*************************************************************************\n");
			__DSVERIFIER_assert(0);
		}
	}
	if (PROPERTY == TIMING){
		if (PROPERTY == TIMING){
			if (hw.clock == 0l){
				printf("\n\n***************************\n");
				printf("* Clock could not be zero *\n");
				printf("***************************\n");
				__DSVERIFIER_assert(0);
			}
			hw.cycle = ((double) 1.0 / hw.clock);
			if (hw.cycle < 0){
				printf("\n\n*********************************************\n");
				printf("* The cycle time could not be representable *\n");
				printf("*********************************************\n");
				__DSVERIFIER_assert(0);
			}
			if (ds.sample_time == 0){
				printf("\n\n*****************************************************************************\n");
				printf("* You need to inform the sample time of the digital system (ds.sample_time) *\n");
				printf("*****************************************************************************\n");
				__DSVERIFIER_assert(0);
			}
		}
	}
}

/** method to call the verification task considering or not the uncertainty for digital system (ds struct) */
void call_verification_task(void * verification_task){

	/* delta transformation don't support uncertainty */
	if ((REALIZATION == DDFI) || (REALIZATION == DDFII) || (REALIZATION == TDDFII)){
		printf("\n\n**********************************************************************************\n");
		printf("* It is not possible to use uncertainty parameters with delta transformation yet *\n");
		printf("**********************************************************************************\n");
		assert(0);
	}

	/* Base case is the execution using all parameters without uncertainty */
	_Bool base_case_executed = 0;

	/* Considering uncertainty for numerator coefficients */
	int i=0;
	for(i=0; i<ds.b_size; i++){
		double factor = ((ds.b[i] * ds.b_uncertainty[i]) / 100);
		factor = factor < 0 ? factor * (-1) : factor;

		double min = ds.b[i] - factor;
		double max = ds.b[i] + factor;

		/* Eliminate redundant executions  */
		if ((factor == 0) && (base_case_executed == 1)){
			continue;
		}else if ((factor == 0) && (base_case_executed == 0)){
			base_case_executed = 1;
		}

		ds.b[i] = nondet_double();
		__DSVERIFIER_assume((ds.b[i] >= min) && (ds.b[i] <= max));
	}

	 /* considering uncertainty for denominator coefficients */
	for(i=0; i<ds.a_size; i++){
		double factor = ((ds.a[i] * ds.a_uncertainty[i]) / 100);
		factor = factor < 0 ? factor * (-1) : factor;

		double min = ds.a[i] - factor;
		double max = ds.a[i] + factor;

		/* Eliminate redundant executions  */
		if ((factor == 0) && (base_case_executed == 1)){
			continue;
		}else if ((factor == 0) && (base_case_executed == 0)){
			base_case_executed = 1;
		}

		ds.a[i] = nondet_double();
		__DSVERIFIER_assume((ds.a[i] >= min) && (ds.a[i] <= max));
	}
	((void(*)())verification_task)(); /* call the verification task */
}

/** call the closedloop verification task */
void call_closedloop_verification_task(void * closedloop_verification_task){

	/* delta transformation doesn't support uncertainty */
	if ((REALIZATION == DDFI) || (REALIZATION == DDFII) || (REALIZATION == TDDFII)){
		printf("\n\n**********************************************************************************\n");
		printf("* It is not possible to use uncertainty parameters with delta transformation yet *\n");
		printf("**********************************************************************************\n");
		__DSVERIFIER_assert(0);
	}

	/* base case is the execution using all parameters without uncertainty */
	_Bool base_case_executed = 0;

	/* considering uncertainty for numerator coefficients */
	int i=0;
	for(i=0; i<plant.b_size; i++){
		double factor = ((plant.b[i] * plant.b_uncertainty[i]) / 100);
		factor = factor < 0 ? factor * (-1) : factor;
		double min = plant.b[i] - factor;
		double max = plant.b[i] + factor;

		/* Eliminate redundant executions  */
		if ((factor == 0) && (base_case_executed == 1)){
			continue;
		}else if ((factor == 0) && (base_case_executed == 0)){
			base_case_executed = 1;
		}

		plant.b[i] = nondet_double();
		__DSVERIFIER_assume((plant.b[i] >= min) && (plant.b[i] <= max));
	}

	/* considering uncertainty for denominator coefficients */
	for(i=0; i<plant.a_size; i++){
		double factor = ((plant.a[i] * plant.a_uncertainty[i]) / 100);
		factor = factor < 0 ? factor * (-1) : factor;

		double min = plant.a[i] - factor;
		double max = plant.a[i] + factor;

		/* eliminate redundant executions  */
		if ((factor == 0) && (base_case_executed == 1)){
			continue;
		}else if ((factor == 0) && (base_case_executed == 0)){
			base_case_executed = 1;
		}

		plant.a[i] = nondet_double();
		__DSVERIFIER_assume((plant.a[i] >= min) && (plant.a[i] <= max));
	}

	/* call the verification task */
	((void(*)())closedloop_verification_task)(); 
}
