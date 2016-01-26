#include "../../../bmc/core/definitions.h"
#include "../../../bmc/core/compatibility.h"
#include "../../../bmc/core/util.h"

int main(){
	double y[11] = { 0.5, 1.0, 0.5, 1.1, 0.0, 1.0, 0.5, -0.5, 0.5, -0.5, 1.0 };
	int y_size = 11;
	double_check_oscillations(y,y_size);
}
