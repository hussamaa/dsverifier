/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *                Iury Bessa     <iury.bessa@gmail.com>
 *                Renato Abreu   <renatobabreu@yahoo.com.br>
 *
 * ------------------------------------------------------
 *
 * compatibility functions
 *
 * ------------------------------------------------------
*/

#include <stdlib.h>
#include <assert.h>

void __DSVERIFIER_assume(_Bool expression){
	#if  (BMC == ESBMC)
		__ESBMC_assume(expression);
	#elif(BMC == CBMC)
		__CPROVER_assume(expression);
	#else
		printf("BMC NOT SUPPORTED");
		assert(0);
	#endif
}

void __DSVERIFIER_assert(_Bool expression){
	assert(expression);
}
