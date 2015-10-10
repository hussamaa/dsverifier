/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *                Iury Bessa     <iury.bessa@gmail.com>
 *                Renato Abreu   <renatobabreu@yahoo.com.br>
 *                Felipe Monteiro <felipemonteiro@ufam.edu.br>
 *
 * ------------------------------------------------------
 *
 * Space state representation for DSVerifier
 *
 * ------------------------------------------------------
*/

extern digital_system_space_state _controller;

extern int rowA;
extern int columnA;
extern int rowB;
extern int columnB;
extern int rowC;
extern int columnC;
extern int rowD;
extern int columnD;
extern int rowInputs;
extern int columnInputs;
extern int rowStates;
extern int columnStates;
extern int rowOutputs;
extern int columnOutputs;

void space_state_representation(void){

    //double resultX[LIMIT][LIMIT];
    //double resultY[LIMIT][LIMIT];

    double result1[LIMIT][LIMIT];
    double result2[LIMIT][LIMIT];



    int i, j, k;
    for(i=0; i<LIMIT;i++){
       for(j=0; j<LIMIT;j++){
        //resultX[i][j]=0;
        //resultY[i][j]=0;
        result1[i][j]=0;
        result2[i][j]=0;
       }
    }


    //for(i=0; i<_controller.rowStates;i++){
    //   for(j=0; j<_controller.columnStates;j++){
    //    resultX[i][j]= _controller.states[i][j];
    //   }
    //}

    matrix_multiplication(rowC,columnC,rowStates,columnStates,_controller.C,_controller.states,result1);
    matrix_multiplication(rowD,columnD,rowInputs,columnInputs,_controller.D,_controller.inputs,result2);

     add_matrix(rowC,
    		   columnStates,
               result1,
               result2,
               _controller.outputs);

    //resultY[0][0] = _controller.outputs[0][0];


     for (i = 1; i < K_SIZE; i++) {
    	matrix_multiplication(rowA,columnA,rowStates,columnStates,_controller.A,_controller.states,result1);
    	matrix_multiplication(rowB,columnB,rowInputs,columnInputs,_controller.B,_controller.inputs,result2);

    	add_matrix(rowA,
    			   columnStates,
                   result1,
                   result2,
                   _controller.states);

        //resultX[i][0] = _controller.states[0][0];
        //resultX[i][1] = _controller.states[1][0];


        matrix_multiplication(rowC,columnC,rowStates,columnStates,_controller.C,_controller.states,result1);
        matrix_multiplication(rowD,columnD,rowInputs,columnInputs,_controller.D,_controller.inputs,result2);

        add_matrix(rowC,
        		   columnStates,
                   result1,
                   result2,
                   _controller.outputs);


        //resultY[0][i] = _controller.outputs[0][0];
    }

}
