#include <dsverifier.h>

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
        .b = { 2.0, -4.0 },
        .b_size = 2,
        .a = { 1.0, -0.1, -0.3 },
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

int unit_test(){

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
   assert(c_num_qtz[0] == 0.0099945068359375);
   assert(c_num_qtz[1] == -0.0050048828125);
   assert(c_num_qtz[2] == -0.0034027099609375);
   assert(c_num_qtz[3] == 0.00079345703125);

   assert(c_den_qtz[0] == 1.0);
   assert(c_den_qtz[1] == 0.399993896484375);
   assert(c_den_qtz[2] == -0.19000244140625);
   assert(c_den_qtz[3] == 0.014007568359375);
   assert(c_den_qtz[4] == 0);

}
