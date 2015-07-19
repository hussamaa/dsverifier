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
 * delta operator transformation
 *
 * ------------------------------------------------------
*/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>

int binomial_coefficient(int n, int p){
   return fatorial(n) / (fatorial(p) * fatorial(n-p));
}

void binomial(int degree, double delta, double out[]){
   initialize_array(out, 3);
   int i;
   for(i=0; i<=degree; i++){
	  out[degree-i] = binomial_coefficient(degree, i) * internal_pow(delta, degree-i);
   }
}

/** calculate the delta coefficients for a polynomial */
void generate_delta_coefficients(double vetor[], double out[], int n, double delta){
   initialize_array(out,n);
   double a_invertido[n];
   initialize_array(a_invertido,n);
   revert_array(vetor, a_invertido, n);
   double _a[n];
   initialize_array(_a,n);
   int i,j;
   for(i=0; i < n; i++){
	  double b[n+1];
	  initialize_array(b,n+1);
	  binomial(i, delta, b);
	  for(j=0; j<i+1; j++){
		 b[j] = b[j] * a_invertido[i];
		 _a[j] = _a[j] + b[j];
	  }
   }
   revert_array(_a, out, n);
}
