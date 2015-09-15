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

/** calculate the delta coefficients for a polynomial */
void generate_delta_coefficients_with_base(double vetor[], double out[], int n, double delta){
	generate_delta_coefficients(vetor, out, n, delta);
	int i;
	double base = out[0];
	for(i=0; i<n; i++){
		out[i] = out[i] / base;
	}
}

/* get a transfer function in delta domain */
void get_delta_transfer_function(double b[], double b_out[], int b_size, double a[], double a_out[], int a_size, double delta){
	/* generate delta coefficients */
	generate_delta_coefficients(b, b_out, b_size, delta);
	generate_delta_coefficients(a, a_out, a_size, delta);
	int i = 0;
	double base = a_out[0];
	/** applying base in numerator coefficients */
	for (i=0; i < b_size; i++){
		b_out[i] = b_out[i] / base;
	}
	for (i=0; i < a_size; i++){
		a_out[i] = a_out[i] / base;
	}
}
