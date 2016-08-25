#include <dsverifier.h>

int unit_test(){
	double y[10] = { 2, 2, 2, 4, 4, 4, 2, 2, 2, 4};
	int y_size = 10;
	double_check_persistent_limit_cycle(y, y_size);
}
