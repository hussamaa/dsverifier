#include <dsverifier.h>

implementation impl = {
	.int_bits = 16,
	.frac_bits = 4,
};

int unit_test(){

	initialization();

	overflow_mode = WRAPAROUND;
	rounding_mode = FLOOR;

	double value[5] = {-1.87238712461624, -3.18287581623761, -9.6712387123123, -3.1872837817283, -9.99999999999999};
	double value_qtz_matlab[5] = {-1.875000000000000, -3.187500000000000, -9.687500000000000, -3.187500000000000, -10.000000000000000};

	fxp_t value_fxp[5];
	fxp_double_to_fxp_array(value, value_fxp, 5);

	double value_qtz_dsverifier[5];
	fxp_to_double_array(value_qtz_dsverifier, value_fxp, 5);

	__DSVERIFIER_assert(value_qtz_matlab[0] == value_qtz_dsverifier[0]);
	__DSVERIFIER_assert(value_qtz_matlab[1] == value_qtz_dsverifier[1]);
	__DSVERIFIER_assert(value_qtz_matlab[2] == value_qtz_dsverifier[2]);
	__DSVERIFIER_assert(value_qtz_matlab[3] == value_qtz_dsverifier[3]);
	__DSVERIFIER_assert(value_qtz_matlab[4] == value_qtz_dsverifier[4]);

}
