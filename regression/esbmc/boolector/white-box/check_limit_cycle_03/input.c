#include <dsverifier.h>

int unit_test(){
	double y[6] = { -0.5, 0.5, -0.5, 0.5, -0.5, 0.5 };
	int y_size = 6;
	double_check_limit_cycle(y, y_size);
}
