#include "../../../../bmc/core/compatibility.h"
#include "../../../../bmc/core/util.h"

int main(){
	double y[17] = { 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 150, 2, 150 };
	int y_size = 17;
	double_check_limit_cycle(y, y_size);
}
