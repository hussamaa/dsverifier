#include "../../../bmc/dsverifier.h"

digital_system_state_space _controller;

implementation impl = {
	.int_bits = 15,
	.frac_bits = 16
};

int rowA = 2;
int columnA = 2;
int rowB = 2;
int columnB = 1;
int rowC = 1;
int columnC = 2;
int rowD = 1;
int columnD = 1;
int rowInputs = 1;
int columnInputs = 1;
int rowStates = 2;
int columnStates = 1;
int rowOutputs = 1;
int columnOutputs = 1;
double error_limit = 0.001018;

void initials(){

    _controller.A[0][0] = 2.0;
    _controller.A[0][1] = -1.0;
    _controller.A[1][0] = 1.0;
    _controller.A[1][1] = 5.0;

    _controller.B[0][0] = 0.0;
    _controller.B[1][0] = 1.5;

    _controller.C[0][0] = 1.0;
    _controller.C[0][1] = 0.6;

    _controller.D[0][0] = 0.0;

    _controller.inputs[0][0] = 1.0;

}
