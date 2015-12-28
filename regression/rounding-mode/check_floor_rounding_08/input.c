#include "../../../bmc/core/definitions.h"
#include "../../../bmc/core/compatibility.h"
#include "../../../bmc/core/fixed-point.h"
#include "../../../bmc/core/util.h"
#include "../../../bmc/core/functions.h"
#include "../../../bmc/core/realizations.h"
#include "../../../bmc/core/delta-operator.h"
#include "../../../bmc/core/closed-loop.h"
#include "../../../bmc/core/initialization.h"

implementation impl = {
	.int_bits = 15,
	.frac_bits = 4,
};

int main(){

	initialization();

	OVERFLOW_MODE = WRAPAROUND;
	ROUNDING_MODE = FLOOR;

	double value[4] = {1.000000000000000, -2.625000000000000, 2.125000000000000, -0.625000000000000};
	double value_qtz_matlab[4] = {1.000000000000000, -2.625000000000000, 2.125000000000000, -0.625000000000000};

	fxp_t value_fxp[4];
	fxp_double_to_fxp_array(value, value_fxp, 4);

	double value_qtz_dsverifier[4];
	fxp_to_double_array(value_qtz_dsverifier, value_fxp, 4);

	__DSVERIFIER_assert(value_qtz_matlab[0] == value_qtz_dsverifier[0]);
	__DSVERIFIER_assert(value_qtz_matlab[1] == value_qtz_dsverifier[1]);
	__DSVERIFIER_assert(value_qtz_matlab[2] == value_qtz_dsverifier[2]);
	__DSVERIFIER_assert(value_qtz_matlab[3] == value_qtz_dsverifier[3]);

}
