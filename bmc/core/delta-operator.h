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
}

/*returns the binomial coefficient, defined as n!/((n–k)! k!). This is the number of combinations of n items taken k at a time.*/
int nchoosek(int n, int k){

if (k == 0) 
  return 1;

return (n * nchoosek(n - 1, k - 1)) / k;

}

/* get a digital system represented in transfer function and transform in delta form */
void get_delta_transfer_function_with_base(double b[], double b_out[], int b_size, double a[], double a_out[], int a_size, double delta){
	int i,j;
	int N = a_size - 1;
	int M = b_size - 1;
	double sum_delta_operator;

	/*delta form for denominator*/
	for(i=0; i<=N; i++)
	{
	sum_delta_operator = 0;
	  for(j=0; j<=i; j++)
 	  {
		sum_delta_operator = sum_delta_operator + a[j]*nchoosek(N-j,i-j);
	  }
	a_out[i] = pow(delta,N-i)*sum_delta_operator;
	}

	/*delta form for numerator*/
	for(i=0; i<=M; i++)
	{
	sum_delta_operator = 0;
	  for(j=0; j<=i; j++)
 	  {
		sum_delta_operator = sum_delta_operator + b[j]*nchoosek(M-j,i-j);
	  }
	b_out[i] = pow(delta,M-i)*sum_delta_operator;
	}
}
