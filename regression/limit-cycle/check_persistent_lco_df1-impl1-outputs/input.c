#include "../../../bmc/core/definitions.h"
#include "../../../bmc/core/compatibility.h"
#include "../../../bmc/core/fixed-point.h"
#include "../../../bmc/core/util.h"
#include "../../../bmc/core/functions.h"
#include "../../../bmc/core/realizations.h"
#include "../../../bmc/core/delta-operator.h"
#include "../../../bmc/core/closed-loop.h"
#include "../../../bmc/core/initialization.h"

digital_system ds = {
	.b = { -1.553, 3.119, -1.566 },
	.b_size = 3,
	.a = { 1.00000000, 0.0387300, -0.96 },
	.a_size = 3,
	.sample_time = 0.005
};

implementation impl = {
	.int_bits = 15,
	.frac_bits = 4,
	.min = -6.0,
	.max = 6.0
};

int x_size = 10;

int main(){

	initialization();
	OVERFLOW_MODE = WRAPAROUND;

	fxp_t a_fxp[ds.a_size];
	fxp_t b_fxp[ds.b_size];

	/* quantize the denominator using fxp */
	fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);

	/* quantize the numerator using fxp */
	fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);

	fxp_t min_fxp = fxp_double_to_fxp(impl.min);
	fxp_t max_fxp = fxp_double_to_fxp(impl.max);

	fxp_t y[10];
	fxp_t x[] = { -54, -54, -54, -54, -54, -54, -54, -54, -54, -54 };

	int i;
	for (i = 0; i < x_size; ++i) {
		y[i] = 0;
	}
	fxp_t xaux[ds.b_size];
	for (i = 0; i < ds.b_size; ++i) {
		xaux[i] = -54;
	}

	/* prepare the previous states */
	fxp_t yaux[ds.a_size];
	yaux[0] = 0;
	yaux[1] = -3;
	yaux[2] = -23;

	for(i=0; i<x_size; ++i){
		shiftL(x[i], xaux, ds.b_size);
		y[i] = fxp_direct_form_1(yaux, xaux, a_fxp, b_fxp, ds.a_size, ds.b_size);
		y[i] = fxp_quantize(y[i]);
		shiftL(y[i], yaux, ds.a_size);
	}

	__DSVERIFIER_assert(y[0] == -3);
	__DSVERIFIER_assert(y[1] == -23);
	__DSVERIFIER_assert(y[2] == -3);
	__DSVERIFIER_assert(y[3] == -23);
	__DSVERIFIER_assert(y[4] == -3);
	__DSVERIFIER_assert(y[5] == -23);
	__DSVERIFIER_assert(y[6] == -3);
	__DSVERIFIER_assert(y[7] == -23);
	__DSVERIFIER_assert(y[8] == -3);
	__DSVERIFIER_assert(y[9] == -23);

}
