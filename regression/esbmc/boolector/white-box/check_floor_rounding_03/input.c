#include <dsverifier.h>

digital_system ds = {
	.b = { -1.553, 3.119, -1.566 },
	.b_size = 3,
	.a = { 1.00000000, 0.0387300, -0.96 },
	.a_size = 3,
	.sample_time = 0.005
};

implementation impl = {
	.int_bits = 15,
	.frac_bits = 12,
	.min = -6.0,
	.max = 6.0
};

int unit_test(){

	initialization();

	OVERFLOW_MODE = WRAPAROUND;
	ROUNDING_MODE = FLOOR;

	fxp_t a_fxp[ds.a_size];
	fxp_t b_fxp[ds.b_size];

	/* quantize the numerator using fxp */
	fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);

	/* quantize the denominator using fxp */
	fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);

	double b_qtz[ds.b_size];
	double a_qtz[ds.a_size];

	fxp_to_double_array(b_qtz, b_fxp, ds.b_size);
	fxp_to_double_array(a_qtz, a_fxp, ds.a_size);

	__DSVERIFIER_assert(b_qtz[0] == -1.55322265625);
	__DSVERIFIER_assert(b_qtz[1] ==  3.118896484375);
	__DSVERIFIER_assert(b_qtz[2] == -1.566162109375);

	__DSVERIFIER_assert(a_qtz[0] == 1.0);
	__DSVERIFIER_assert(a_qtz[1] == 0.03857421875);
	__DSVERIFIER_assert(a_qtz[2] == -0.960205078125);

}
