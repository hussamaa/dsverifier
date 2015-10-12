#include <assert.h>

#include "../../../bmc/core/definitions.h"
#include "../../../bmc/core/compatibility.h"
#include "../../../bmc/core/fixed-point.h"
#include "../../../bmc/core/realizations.h"
#include "../../../bmc/core/util.h"
#include "../../../bmc/core/functions.h"
#include "../../../bmc/core/initialization.h"
#include "../../../bmc/core/closed-loop.h"

digital_system control = {
	.b = { 2020.0, -3254.0, -126.1, 2096.0, -735.9 },
	.b_size = 4,
	.a = { 1.0, -2.9, 2.8, -0.9 },
	.a_size = 4,
	.sample_time = 0.1
};

implementation impl = {
	.int_bits = 15,
	.frac_bits = 16
};

double nondet_double();

int main(){
	
	/* plant model */
	double mass = 0.3;
	/*
	double mass = nondet_double();
	__DSVERIFIER_assume(mass >= 0.1 && mass <= 0.5);
	*/

	double M = 0.5;
	double b = 0.1;
	double I = 0.006;
	double g = 9.8;
	double l = 0.6;

	double q = (M + mass) * (I+mass*internal_pow(l,2)) - internal_pow((mass*l),2);
	double plant_num[100];
	double plant_den[100];

	plant_num[0] = mass*l/q ;
	plant_num[1] = 0;

	plant_den[0] = 1.0;
	plant_den[1] = b*(I+mass*internal_pow(l,2))/q;
	plant_den[2] = -(M+mass)*mass*g*l/q;
	plant_den[3] = -b*mass*g*l/q;

	int plant_num_size = 2;
	int plant_den_size = 4;

	initialization();

	/* generating closed loop for series or feedback */
	double * c_num = control.b;
	int c_num_size = control.b_size;
	double * c_den = control.a;
	int c_den_size = control.a_size;

	/* quantizing controller coefficients */
	fxp32_t c_num_fxp[control.b_size];
	fxp_double_to_fxp_array(c_num, c_num_fxp, control.b_size);
	fxp32_t c_den_fxp[control.a_size];
	fxp_double_to_fxp_array(c_den, c_den_fxp, control.a_size);

	/* getting quantized controller coefficients  */
	double c_num_qtz[control.b_size];
	fxp_to_double_array(c_num_qtz, c_num_fxp, control.b_size);
	double c_den_qtz[control.a_size];
	fxp_to_double_array(c_den_qtz, c_den_fxp, control.a_size);

	/* getting plant coefficients */
	double * p_num = plant_num;
	int p_num_size = plant_num_size;
	double * p_den = plant_den;
	int p_den_size = plant_den_size;

	double ans_num[100];
	int ans_num_size = control.b_size + p_num_size - 1;
	double ans_den[100];
	int ans_den_size = control.a_size + p_den_size - 1;

	ft_closedloop_series(c_num_qtz, c_num_size, c_den_qtz, c_den_size, p_num, p_num_size, p_den, p_den_size, ans_num, ans_num_size, ans_den, ans_den_size);

	/* checking stability */
	printf("Verifying stability for closedloop function\n");
	__DSVERIFIER_assert(check_stability_closedloop(ans_den, ans_den_size, p_num, p_num_size, p_den, p_den_size));

	return 0;

}
