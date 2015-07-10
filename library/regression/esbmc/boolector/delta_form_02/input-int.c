#include <stdlib.h>
#include <verificationfxp.h>

digital_system ds = {
        .a = { 1.0, -1.9, 0.8925 },
        .a_size = 3,
};

implementation impl = {
	.delta = 0.1
};

int main(){
	double da[3];
	__DSVERIFIER_generate_delta_coefficients(ds.a, da, impl.delta);
	return 0;
}
