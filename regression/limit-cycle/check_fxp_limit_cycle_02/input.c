#include "../../../bmc/core/definitions.h"
#include "../../../bmc/core/compatibility.h"
#include "../../../bmc/core/fixed-point.h"
#include "../../../bmc/core/functions.h"
#include "../../../bmc/core/util.h"

int main(){
	fxp_t y[6] = { 4, 2, 4, 2, 4, 2 };
	int y_size = 6;
	fxp_check_persistent_limit_cycle(y, y_size);
}
