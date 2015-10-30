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
 * util functions for DSVerifier
 *
 * ------------------------------------------------------
*/

#include <stdio.h>
#include <stdlib.h>

/** initialise an array with zeroes */
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

/** a simplify equivalent for Math.pow() */
double internal_pow(double a, double b){
   int i;
   double acc = 1;
   for (i=0; i < b; i++){
	  acc = acc*a;
   }
   return acc;
}

/** a simplify equivalent for Math.abs() */
double internal_abs(double a){
   return a < 0 ? -a : a;
}

/** calculate the factorial of a number */
int fatorial(int n){
   return n == 0 ? 1 : n * fatorial(n-1);
}

/** check stability for a polynomial using jury criteria */
int check_stability(double a[], int n){
   int lines = 2 * n - 1;
   int columns = n;
   double m[lines][n];
   int i,j;

   /* to put current values in stability counter-example 
    * look for current_stability (use: --no-slice) */
   double current_stability[n];
   for (i=0; i < n; i++){
	   current_stability[i] = a[i];
   }

   /* check the first constraint condition F(1) > 0 */
   double sum = 0;
   for (i=0; i < n; i++){
	   sum += a[i];
   }
   if (sum <= 0){
	printf("[DEBUG] the first constraint of Jury criteria failed: (F(1) > 0)");
	   return 0;
   }

   /* check the second constraint condition F(-1)*(-1)^n > 0 */
   sum = 0;
   for (i=0; i < n; i++){
 	  sum += a[i] * internal_pow(-1, n-1-i);
   }
   sum = sum * internal_pow(-1, n-1);
   if (sum <= 0){
	  printf("[DEBUG] the second constraint of Jury criteria failed: (F(-1)*(-1)^n > 0)");
	  return 0;
   }

   /* check the third constraint condition abs(a0 < an*(z^n)  */
   if (internal_abs(a[n-1]) > a[0]){
	   printf("[DEBUG] the third constraint of Jury criteria failed: (abs(a0) < a_{n}*z^{n})");
	   return 0;
   }

   /* check the fourth constraint of condition (Jury Table) */
   for (i=0; i < lines; i++){
	  for (j=0; j < columns; j++){
		 m[i][j] = 0;
	  }
   }
   for (i=0; i < lines; i++){
	  for (j=0; j < columns; j++){
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
			m[i][j] = m[i-2][j] - (m[i-2][columns] / m[i-2][0]) * m[i-1][j];
		 }
	  }
   }
   int first_is_positive =  m[0][0] >= 0 ? 1 : 0;
   for (i=0; i < lines; i++){
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

/**
 * The array ans will receive the sum a + b.
 * The arrays a and must be in the crescent degree order (e.g.: a0*1+a_1*x^1+a2*x^3...)
 * The result will be stored in ans[] and the size of ans[] will be stored in Nans.
 */
void poly_sum(double a[], int Na, double b[], int Nb, double ans[], int Nans){
	int i;
	Nans = Na>Nb? Na:Nb;

	for (i=0; i<Nans; i++){
		if (Na>Nb){
			ans[i]=a[i];
			if (i > Na-Nb-1){
				ans[i]=ans[i]+b[i-Na+Nb];
			}
		}else {
			ans[i]=b[i];
			if (i> Nb - Na -1){
				ans[i]=ans[i]+a[i-Nb+Na];
			}
		}
	}
}

/**
 * The array ans will receive the product a*b.
 * The arrays a and must be in the crescent degree order (e.g.: a0*1+a_1*x^1+a2*x^3...)
 * The result will be stored in ans[] and the size of ans[] will be stored in Nans.
 */
void poly_mult(double a[], int Na, double b[], int Nb, double ans[], int Nans){
	int i;
	int j;
	int k;
	Nans = Na+Nb-1;

	for (i=0; i<Na; i++){
		for (j=0; j<Nb; j++){
			k= Na + Nb - i - j - 2;
			ans[k]=0;
		}
	}

	for (i=0; i<Na; i++){
		for (j=0; j<Nb; j++){
			k= Na + Nb - i - j - 2;
			ans[k]=ans[k]+a[Na - i - 1]*b[Nb - j - 1];
		}
	}
}

/** function to check oscillations in an array (used in limit cycle property) */
void double_check_oscillations(double * y, int y_size){
	/* check if the first elements are the same, and if last repeats */
	__DSVERIFIER_assume(y[0] != y[y_size - 1]);
	int window_timer = 0;
	int window_count = 0;
	int i, j;
	for (i = 2; i < y_size; i++){
		int window_size = i;
		for(j=0; j<y_size; j++){
			if (window_timer > window_size){
				window_timer = 0;
				window_count = 0;
			}
			/* check bound of outputs */
			int window_index = j + window_size;
			if (window_index < y_size){
				/* check if window occurs */
				if (y[j] == y[window_index]){
					window_count++;
					/* window_count == window_size (the repeats occurs) */
					assert(!(window_count == window_size));
				}
			}else{
				break;
			}
			window_timer++;
		}
	}
}

/* verify limit_cycle oscillations in last outputs */
void double_check_limit_cycle(double * y, int y_size){
	/* last element is the reference */
	double reference = y[y_size - 1];
	int idx = 0;
	int window_size = 1;
	/* find window size */
	for(idx = (y_size-2); idx >= 0; idx--){
		if (y[idx] != reference){
			window_size++;
		}else{
			break;
		}
	}
	/* check if there is at least one repetition */
	__DSVERIFIER_assume(window_size != y_size && window_size != 1);
	printf("window_size %d\n", window_size);
	int desired_elements = 2 * window_size;
	int found_elements = 0;
	/* check if final oscillations occurs */
	for(idx = (y_size-1); idx >= 0; idx--){
		if (idx > (y_size-window_size-1)){
			printf("%.0f == %.0f\n", y[idx], y[idx-window_size]);
			int cmp_idx = idx - window_size;
			if ((cmp_idx > 0) && (y[idx] == y[idx-window_size])){
				found_elements = found_elements + 2;
			}else{
				break;
			}
		}
	}
	printf("desired_elements %d\n", desired_elements);
	printf("found_elements %d\n", found_elements);
	__DSVERIFIER_assert(desired_elements != found_elements);
}

/* verify limit_cycle oscillations in last outputs */
void double_check_persistent_limit_cycle(double * y, int y_size){

	/* last element is the reference */
	double reference = y[y_size - 1];
	int idx = 0;
	int window_size = 1;

	/* find window size */
	for(idx = (y_size-2); idx >= 0; idx--){
		if (y[idx] != reference){
			window_size++;
		}else{
			break;
		}
	}

	/* check if there is at least one repetition */
	__DSVERIFIER_assume(window_size != y_size && window_size != 1);
	printf("window_size %d\n", window_size);
	int desired_elements = 2 * window_size;
	double lco_elements[desired_elements];
	int lco_elements_index = desired_elements - 1;
	int found_elements = 0;

	/* check if final oscillations occurs */
	for(idx = (y_size-1); idx >= 0; idx--){
		if (idx > (y_size-window_size-1)){
			printf("%.0f == %.0f\n", y[idx], y[idx-window_size]);
			int cmp_idx = idx - window_size;
			if ((cmp_idx > 0) && (y[idx] == y[idx-window_size])){
				lco_elements[lco_elements_index--];
				found_elements = found_elements + 2;
			}else{
				break;
			}
		}
	}
	printf("desired_elements %d\n", desired_elements);
	printf("found_elements %d\n", found_elements);

	/* check if the window was confirmed */
	__DSVERIFIER_assume(desired_elements == found_elements);

	/* check if there is a persistent lco */
	idx = y_size - 1;
	int lco_aux_idx = desired_elements - 1;
	_Bool is_persistent = 0;
	while (idx >= 0){
		if(y[idx--] == lco_elements[lco_aux_idx--]){
			is_persistent = 1;
		}else{
			is_persistent = 0;
			break;
		}
		/* reset the aux index */
		if (lco_aux_idx == -1){
			lco_aux_idx = desired_elements - 1;
		}
	}
	__DSVERIFIER_assert(is_persistent == 0);
}

/* print array elements */
void print_array_elements(char * name, double * v, int n){
   printf("%s = {", name);
   int i;
   for(i=0; i < n; i++){
      printf(" %.32f ", v[i]);
   }
   printf("}\n");
}

/* adds two matrices */
void double_add_matrix( unsigned int lines,  unsigned int columns, double m1[LIMIT][LIMIT], double m2[LIMIT][LIMIT], double result[LIMIT][LIMIT]){
	unsigned int i, j;
    for (i = 0; i < lines; i++)
    	for (j = 0; j < columns; j++) result[i][j] = m1[i][j] + m2[i][j];
}

/* multiplies two matrices */
void double_matrix_multiplication( unsigned int i1, unsigned int j1, unsigned int i2, unsigned int j2, double m1[LIMIT][LIMIT], double m2[LIMIT][LIMIT], double m3[LIMIT][LIMIT]){

	unsigned int i, j, k;
    if (j1 == i2) { //Checking if the multiplication is possible
        // Initialising Matrix 3
        for (i=0; i<i1; i++) {
            for (j=0; j<j2; j++) {
                m3[i][j] = 0;
            }
        }
        //Calculating multiplication result
        for (i=0;i<i1; i++) {
            for (j=0; j<j2; j++) {
                for (k=0; k<j1; k++) {
                    //printf("i: %d \t j: %d\n", i,j);
                    m3[i][j] = m3[i][j] + (m1[i][k] * m2[k][j]);
                }
                //printf("m3[%d][%d]: %d\n", i,j,m3[i][j]);
            }
        }
    } else {
        printf("\nError! Operation invalid, please enter with valid matrices.\n");
    }
}

/* multiplies two matrices, fixed point version */
void fxp_matrix_multiplication( unsigned int i1, unsigned int j1, unsigned int i2, unsigned int j2, fxp32_t m1[LIMIT][LIMIT], fxp32_t m2[LIMIT][LIMIT], fxp32_t m3[LIMIT][LIMIT]){
	unsigned int i, j, k;
    if (j1 == i2) { //Checking if the multiplication is possible
        // Initialising Matrix 3
        for (i=0; i<i1; i++) {
            for (j=0; j<j2; j++) {
                m3[i][j] = 0;
            }
        }
        //Calculating multiplication result
        for (i=0;i<i1; i++) {
            for (j=0; j<j2; j++) {
                for (k=0; k<j1; k++) {
                    //printf("i: %d \t j: %d\n", i,j);
                    m3[i][j] = fxp_add( m3[i][j], fxp_mult(m1[i][k] , m2[k][j]));
                }
                //printf("m3[%d][%d]: %d\n", i,j,m3[i][j]);
            }
        }
    } else {
        printf("\nError! Operation invalid, please enter with valid matrices.\n");
    }
}

/* adds two matrices, fixed point version */
void fxp_add_matrix( unsigned int lines,  unsigned int columns, fxp32_t m1[LIMIT][LIMIT], fxp32_t m2[LIMIT][LIMIT], fxp32_t result[LIMIT][LIMIT]){
	unsigned int i, j;
    for (i = 0; i < lines; i++)
    	for (j = 0; j < columns; j++) result[i][j] = fxp_add(m1[i][j] , m2[i][j]);
}

/* prints a matrix */
void print_matrix(double matrix[LIMIT][LIMIT], unsigned int lines, unsigned int columns){
    printf("\nMatrix\n=====================\n\n");
    unsigned int i, j;
    for (i=0; i<lines; i++) {
        for (j=0; j<columns; j++) {
            printf("%2.2f ", matrix[i][j]);
        }
        printf("\n");
    }
    printf("\n");
}
