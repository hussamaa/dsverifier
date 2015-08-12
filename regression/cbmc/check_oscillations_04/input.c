#include "../../../bmc/core/definitions.h"
#include "../../../bmc/core/compatibility.h"
#include "../../../bmc/core/util.h"

int main(){
	double y[10] = { 4.0, 3.0, 2.0, 1.0, 0.5, 1.0, -0.5, 0.5, 1.0, -0.5 };
	int y_size = 10;
	double_check_oscillations(y,y_size);
}
