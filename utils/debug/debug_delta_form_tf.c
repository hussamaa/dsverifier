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
	.b = { 2002.0, -4000.0, 1998.0 },
	.b_size = 3,
	.a = { 1.0, 0.0, -1.0 },
	.a_size = 3,	
	.sample_time = 0.001
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
	.delta = 1,
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

	set_overflow_mode = 0;

	double da[ds.a_size];
	double db[ds.b_size];

	print_array_elements("b", ds.b, ds.b_size);
	print_array_elements("a", ds.a, ds.a_size);

	printf("\ndelta: %.5f\n\n", impl.delta);

	get_delta_transfer_function(ds.b, db, ds.b_size, ds.a, da, ds.a_size, impl.delta);
	
	print_array_elements("db", db, ds.b_size);
	print_array_elements("da", da, ds.a_size);

}
