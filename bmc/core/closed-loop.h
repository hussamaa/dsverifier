/**
 * DSVerifier - Digital Systems Verifier (Main)
 *
 * Federal University of Amazonas - UFAM
 *
 * Dynamical systems TF and polynomial operations lib
 *
 * Authors:	Iury Bessa     <iury.bessa@gmail.com>
 *			Hussama Ismail <hussamaismail@gmail.com>
 *
 * ------------------------------------------------------
 *
 * Version 0.1 - Include polynomial basic operations (sum and multiplication) - 15/12/2014
 * Version 0.2 - Closed-loop transfer function (series and feedback compensation) - 17/03/2014
 * Version 1.0 - Include sensitivity function, allowing the disturbance analisys  - 17/03/2014
 *
 * ------------------------------------------------------
*/

#include <stdio.h>
#include <stdint.h>

/**
 * The arrays ans_num and ans_den will receive the product respectively the numerator and denominator.
 * The arrays must be in the crescent degree order (e.g.: a0*1+a_1*x^1+a2*x^3...)
 * Here is calculated the coefficients of the global transfer function of system with series compensation
 */
void ft_closedloop_series(double c_num[], int Nc_num, double c_den[], int Nc_den, double model_num[], int Nmodel_num, double model_den[], int Nmodel_den, double ans_num[], int Nans_num, double ans_den[], int Nans_den){
	Nans_num = Nc_num + Nmodel_num - 1;
	Nans_den = Nc_den + Nmodel_den - 1 ;
	double den_mult [Nans_den];
	poly_mult(c_num, Nc_num, model_num, Nmodel_num, ans_num, Nans_num);
	poly_mult(c_den, Nc_den, model_den, Nmodel_den, den_mult, Nans_den );
	poly_sum(ans_num, Nans_num , den_mult, Nans_den , ans_den, Nans_den);
}

/**
 * The arrays ans_num and ans_den will receive the product respectively the numerator and denominator.
 * The arrays must be in the crescent degree order (e.g.: a0*1+a_1*x^1+a2*x^3...)
 * Here is calculated the coefficients of the global transfer function of system with series compensation
 */
void ft_closedloop_sensitivity(double c_num[], int Nc_num, double c_den[], int Nc_den, double model_num[], int Nmodel_num, double model_den[], int Nmodel_den, double ans_num[], int Nans_num, double ans_den[], int Nans_den){
	int Nans_num_p = Nc_num + Nmodel_num-1;
	Nans_den = Nc_den + Nmodel_den-1;
	Nans_num = Nc_den + Nmodel_den-1;
	double num_mult [Nans_num_p];
	poly_mult(c_den, Nc_den, model_den, Nmodel_den, ans_num, Nans_num);
	poly_mult(c_num, Nc_num, model_num, Nmodel_num, num_mult, Nans_num_p);
	poly_sum(ans_num, Nans_num, num_mult, Nans_num_p, ans_den, Nans_den);
}

/**
 * The arrays ans_num and ans_den will receive the product respectively the numerator and denominator.
 * The arrays must be in the crescent degree order (e.g.: a0*1+a_1*x^1+a2*x^3...)
 * Here is calculated the coefficients of the global transfer function of system with series feedback
 */
void ft_closedloop_feedback(double c_num[], int Nc_num, double c_den[], int Nc_den, double model_num[], int Nmodel_num, double model_den[], int Nmodel_den, double ans_num[], int Nans_num, double ans_den[], int Nans_den){
	Nans_num = Nc_den + Nmodel_num - 1;
	Nans_den = Nc_den + Nmodel_den - 1;
	int Nnum_mult = Nc_num + Nmodel_num - 1;
	double den_mult [Nans_den];
	double num_mult [Nnum_mult];
	poly_mult(c_num, Nc_num, model_num, Nmodel_num, num_mult, Nnum_mult);
	poly_mult(c_den, Nc_den, model_den, Nmodel_den, den_mult, Nans_den);
	poly_sum(num_mult, Nnum_mult, den_mult, Nans_den, ans_den, Nans_den);
	poly_mult(c_den, Nc_den, model_num, Nmodel_num, ans_num, Nans_num);
}

/** check the stability of system using jury criteria */
int check_stability_closedloop(double a[], int n, double plant_num[], int p_num_size, double plant_den[], int p_den_size){
   int columns = n;
   double m[2 * n - 1][n];
   int i,j;
   int first_is_positive = 0;
   double * p_num = plant_num;
   double * p_den = plant_den;
   /* check the first constraint condition F(1) > 0 */
   double sum = 0;
   for (i=0; i < n; i++){
	   sum += a[i];
   }
   __DSVERIFIER_assert(sum > 0);
   /* check the second constraint condition F(-1)*(-1)^n > 0 */
   sum = 0;
   for (i=0; i < n; i++){
 	  sum += a[i] * internal_pow(-1, n-1-i);
   }
   sum = sum * internal_pow(-1, n-1);
   __DSVERIFIER_assert(sum > 0);
   /* check the third constraint condition abs(a0 < an*(z^n)  */
   __DSVERIFIER_assert(internal_abs(a[n-1]) < a[0]);
   /* check the fourth constraint of condition (Jury Table) */
   for (i=0; i < 2 * n - 1; i++){
	  for (j=0; j < columns; j++){
		 m[i][j] = 0;
		 if (i == 0){
			m[i][j] = a[j];
			continue;
		 }
		 if (i % 2 != 0 ){
			 int x;
			 for(x=0; x<columns;x++){
				m[i][x] = m[i-1][columns-x-1];
			 }
			 columns = columns - 1;
			 j = columns;
		 }else{
			__DSVERIFIER_assert(m[i-2][0] > 0);
			m[i][j] = m[i-2][j] - (m[i-2][columns] / m[i-2][0]) * m[i-1][j];
			__DSVERIFIER_assert((m[0][0] >= 0) && (m[i][0] >= 0));
		 }
	  }
   }
   return 1;
}
