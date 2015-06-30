/**
# DSVerifier - Digital Systems Verifier
#
#                Federal University of Amazonas - UFAM
#
# Authors:       Hussama Ismail <hussamaismail@gmail.com>
#                Iury Bessa     <iury.bessa@gmail.com>
#                Renato Abreu   <renatobabreu@yahoo.com.br>
#				 
# ------------------------------------------------------
#
# Util functions for DSVerifier
#
# ------------------------------------------------------
*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

/** initialize an array with zeroes */
void initialize_array(double v[], int n){
   int i;
   for(i=0; i<n; i++){
	   v[i] = 0;
   }
}

/** invert an array */
void revert_array(double v[], double out[], int n){
   initialize_array(out,n);
   int i;
   for(i=0; i<n; i++){
	  out[i] = v[n-i-1];
   }
}

/** an simplify equivalent for Math.pow() */
double internal_pow(double a, double b){
   int i;
   double acc = 1;
   for (i=0; i < b; i++){
	  acc = acc*a;
   }
   return acc;
}

/** calculate the fatorial of a number */
int fatorial(int n){
   return n == 0 ? 1 : n * fatorial(n-1);
}

/** check stability for a polynomial using jury criteria */
int check_stability(double a[], int n){
   int linhas = 2 * n - 1;
   int colunas = n;
   double m[linhas][n];
   int i,j;

   /* to put current values in stability counter-example
	* look for current_stability (use: --no-slice) */
   double current_stability[n];
   for (i=0; i < n; i++){
	   current_stability[i] = a[i];
   }

   for (i=0; i < linhas; i++){
	  for (j=0; j < colunas; j++){
		 m[i][j] = 0;
	  }
   }
   for (i=0; i < linhas; i++){
	  for (j=0; j < colunas; j++){
		 if (i == 0){
			m[i][j] = a[j];
			continue;
		 }
		 if (i % 2 != 0 ){
			 int x;
			 for(x=0; x<colunas;x++){
				m[i][x] = m[i-1][colunas-x-1];
			 }
			 colunas = colunas - 1;
			j = colunas;
		 }else{
			m[i][j] = m[i-2][j] - (m[i-2][colunas] / m[i-2][0]) * m[i-1][j];
		 }
	  }
   }
   int first_is_positive =  m[0][0] >= 0 ? 1 : 0;
   for (i=0; i < linhas; i++){
	  if (i % 2 == 0){
		 int line_is_positive = m[i][0] >= 0 ? 1 : 0;
		 if (first_is_positive != line_is_positive){
			return 0;
		 }
		 continue;
	  }
   }
   return 1;
}

/** check the stability of system using jury criteria */
int check_stability_closedloop(double a[], int n, double plant_num[], int p_num_size, double plant_den[], int p_den_size){
   int colunas = n;
   double m[2 * n - 1][n];
   int i,j;
   int first_is_positive = 0;
   for (i=0; i < 2 * n - 1; i++){
	  for (j=0; j < colunas; j++){
		 m[i][j] = 0;
		 if (i == 0){
			m[i][j] = a[j];
			continue;
		 }
		 if (i % 2 != 0 ){
			 int x;
			 for(x=0; x<colunas;x++){
				m[i][x] = m[i-1][colunas-x-1];
			 }
			 colunas = colunas - 1;
			 j = colunas;
		 }else{
			m[i][j] = m[i-2][j] - (m[i-2][colunas] / m[i-2][0]) * m[i-1][j];
			assert((m[0][0] >= 0) && (m[i][0] >= 0));
		 }
	  }
   }
   return 1;
}
