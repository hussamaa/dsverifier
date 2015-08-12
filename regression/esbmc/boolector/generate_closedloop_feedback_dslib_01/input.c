#include <stdlib.h>
#include "../../../../bmc/core/util.h"
#include "../../../../bmc/core/definitions.h"
#include "../../../../bmc/core/compatibility.h"
#include "../../../../bmc/core/fixed-point.h"
#include "../../../../bmc/core/functions.h"
#include "../../../../bmc/core/realizations.h"
#include "../../../../bmc/core/delta-operator.h"
#include "../../../../bmc/core/closed-loop.h"

digital_system control = {
        .a = { 1.0, 0.4, -0.19, 0.014, 0.0},
        .a_size = 5,
        .b = { 0.01, -0.005, -0.0034, 0.0008 },
        .b_size = 4,
        .sample_time = 0.01
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 16,
        .delta = 0.25,
        .max = 1.0,
        .min = -1.0,
        .scale = 1
};

digital_system plant = {
        .b = { 2.0f, -4.0f },
        .b_size = 2,
        .a = { 1.0f, -0.1f,  -0.3f },
        .a_size = 3
};

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
}

int main(){

   init();

   /* Generating closed loop for series or feedback */
   double c_num[100] = control.b;
   double c_den[100] = control.a;

   /* Quantizing Control Coefficients */
   fxp32_t c_num_fxp[control.b_size];
   fxp_double_to_fxp_array(c_num, c_num_fxp, control.b_size);
   fxp32_t c_den_fxp[control.a_size];
   fxp_double_to_fxp_array(c_den, c_den_fxp, control.a_size);

   /* Getting Control Quantized Coefficients  */
   double c_num_qtz[control.b_size];
   fxp_to_double_array(c_num_qtz, c_num_fxp, control.b_size);
   double c_den_qtz[control.a_size];
   fxp_to_double_array(c_den_qtz, c_den_fxp, control.a_size);

   /* validate quantization  */
   assert(c_num_qtz[0] == 0.0099945068359375f);
   assert(c_num_qtz[1] == -0.0050048828125f);
   assert(c_num_qtz[2] == -0.0034027099609375f);
   assert(c_num_qtz[3] == 0.00079345703125f);

   assert(c_den_qtz[0] == 1.0f);
   assert(c_den_qtz[1] == 0.399993896484375f);
   assert(c_den_qtz[2] == -0.19000244140625f);
   assert(c_den_qtz[3] == 0.014007568359375f);
   assert(c_den_qtz[4] == 0);

   /* Getting Plant Coefficients */
   double p_num[100] = plant.b;
   int p_num_size = plant.b_size;
   double p_den[100] = plant.a;
   int p_den_size = plant.a_size;

   double b_ans[100];
   int b_ans_size = control.a_size + plant.b_size - 1;
   double a_ans[100];
   int a_ans_size = control.a_size + plant.a_size - 1;

   ft_closedloop_feedback(c_num_qtz, control.b_size, c_den_qtz, control.a_size, p_num, p_num_size, p_den, p_den_size, b_ans, b_ans_size, a_ans, a_ans_size);

   assert(a_ans_size == 7);
   assert(b_ans_size == 6);

   assert((float) a_ans[0] == 1.0);
   assert((float) a_ans[1] == 0.3000030517578125);
   assert((float) a_ans[2] == -0.510009765625);
   assert((float) a_ans[3] == -0.1369781494140625);
   assert((float) a_ans[4] == 0.0688018798828125);
   assert((float) a_ans[5] == 0.010986328125);
   assert((float) a_ans[6] == -0.003173828125);

   assert(b_ans[0] == 2); 
   assert(b_ans[1] == -3.20001220703125);
   assert(b_ans[2] == -1.97998046875);
   assert(b_ans[3] == 0.78802490234375);
   assert(b_ans[4] == -0.0560302734375);
   assert(b_ans[5] == 0);

}
