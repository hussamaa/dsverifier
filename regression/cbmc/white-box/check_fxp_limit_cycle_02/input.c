#include <dsverifier.h>

int unit_test(){
	fxp_t y[6] = { 4, 2, 4, 2, 4, 2 };
	int y_size = 6;
	fxp_check_persistent_limit_cycle(y, y_size);
}
