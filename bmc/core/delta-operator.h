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

/*returns the binomial coefficient, defined as n!/((n–k)! k!). This is the number of combinations of n items taken k at a time.*/
int nchoosek(int n, int k){

if (k == 0) 
  return 1;

return (n * nchoosek(n - 1, k - 1)) / k;

}

/** calculate the delta coefficients for a polynomial */
void generate_delta_coefficients(double vetor[], double out[], int n, double delta){
	int i,j;
	int N = n - 1;
	double sum_delta_operator;

	/*delta form for polynomial*/
	for(i=0; i<=N; i++)
	{
	sum_delta_operator = 0;
	  for(j=0; j<=i; j++)
 	  {
		sum_delta_operator = sum_delta_operator + vetor[j]*nchoosek(N-j,i-j);
	  }
	out[i] = internal_pow(delta,N-i)*sum_delta_operator;
	}
}


/* get a transfer function in delta domain */
void get_delta_transfer_function(double b[], double b_out[], int b_size, double a[], double a_out[], int a_size, double delta){
	/* generate delta coefficients */
	generate_delta_coefficients(b, b_out, b_size, delta);
	generate_delta_coefficients(a, a_out, a_size, delta);
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
	a_out[i] = internal_pow(delta,N-i)*sum_delta_operator;
	}

	/*delta form for numerator*/
	for(i=0; i<=M; i++)
	{
	sum_delta_operator = 0;
	  for(j=0; j<=i; j++)
 	  {
		sum_delta_operator = sum_delta_operator + b[j]*nchoosek(M-j,i-j);
	  }
	b_out[i] = internal_pow(delta,M-i)*sum_delta_operator;
	}
}
