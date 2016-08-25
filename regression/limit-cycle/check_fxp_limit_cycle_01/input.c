#include <dsverifier.h>

int unit_test(){
	fxp_t y[17] = { 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 };
	int y_size = 17;
	fxp_check_persistent_limit_cycle(y, y_size);
}
