#include <dsverifier.h>

int unit_test(){
	double y[17] = { 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 };
	int y_size = 17;
	double_check_limit_cycle(y, y_size);
}
