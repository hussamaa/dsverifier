#include <assert.h>

void __DSVERIFIER_assert(_Bool expression){
	assert(expression);
}

void __DSVERIFIER_assume(_Bool expression){
	/* nothing to do here */
}

#include "../bmc/core/definitions.h"
#include "../bmc/core/fixed-point.h"
#include "../bmc/core/realizations.h"
#include "../bmc/core/util.h"
#include "../bmc/core/functions.h"
#include "../bmc/core/initialization.h"
#include "../bmc/core/delta-operator.h"

digital_system ds = { 
	.b = {  0.10000000000000000555111512312578, -0.28189999999999998392397060342773,  0.26369999999999998996358385738858,  -0.08186999999999999833022457096376 },
	.b_size = 4,
	.a = {  1.00000000000000000000000000000000,  -2.57399999999999984368059813277796,  2.18100000000000004973799150320701,  -0.60680000000000000603961325396085  },
	.a_size = 4,
	.sample_time = 0.02
};

/*
digital_system ds = { 
	.b = { 0.012500000000000, 0.004525000000000, -0.000050000000000,  -0.000070000000000 },
	.b_size = 4,
	.a = { 0.125000000000000, 0.106500000000000, 0.016500000000000,  0.000200000000000 },
	.a_size = 4,
	.sample_time = 0.02
};
*/
/*
digital_system ds = { 
	.b = { 0.100000000000000,   0.036200000000000,  -0.000400000000000,  -0.000560000000000 },
	.b_size = 4,
	.a = { 1.000000000000000,   0.852000000000000,   0.132000000000001,   0.001600000000002 },
	.a_size = 4,
	.sample_time = 0.02
};
*/

implementation impl = { 
	.int_bits = 15, 
	.frac_bits = 16,
	.delta = 0.125,
	.max = 1.0,
	.min = -1.0
};

hardware hw = { };

/* inputs */
fxp32_t x_fxp[5];
int x_size = 5;
int generic_timer;

int main(){
	
	initialization();

	OVERFLOW_MODE = 0;

	double da[ds.a_size];
	double db[ds.b_size];

	print_array_elements("a", ds.b, ds.b_size);
	print_array_elements("a", ds.a, ds.a_size);

	printf("\ndelta: %.5f\n\n", impl.delta);

	get_delta_transfer_function(ds.b, db, ds.b_size, ds.a, da, ds.a_size, impl.delta);
	
	print_array_elements("db", db, ds.b_size);
	print_array_elements("da", da, ds.a_size);

}
