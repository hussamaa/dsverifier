#include <dsverifier.h>

int unit_test(){
	double y[8] = {1.0, 1.0, -1.0, -1.0, 1.0, 1.0, -1.0, -1.0 }; 
	int y_size = 8;
	double_check_oscillations(y,y_size);
}
