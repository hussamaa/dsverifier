#include "../../../bmc/core/definitions.h"
#include "../../../bmc/core/compatibility.h"
#include "../../../bmc/core/util.h"

int main(){
	double y[6] = { -0.5, 0.5, -0.5, 0.5, -0.5, 0.5 };
	int y_size = 6;
	double_check_limit_cycle(y, y_size);
}
