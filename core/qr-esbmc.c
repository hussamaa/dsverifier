#include <stdio.h>
#include <stdlib.h>

/* matriz A */
double A[][3] = {
	{ 1, 1, -1 },
	{ 1, 2,  1 },
	{ 1, 2,  1 },
};

int a_m = 3;
int a_n = 3;

typedef struct {
	int m, n;
	double ** v;
} mat_t, * mat;

int main(){

	mat R, Q;

	/* create an copy of matrix A */
	mat x = (mat)malloc(sizeof(mat_t));
	x->v = (double**) malloc (sizeof(double) * a_m);
	x->v[0] = (double *) calloc (sizeof(double), a_m * a_n);
	int i,j;
	for (i = 0; i < a_m; i++)
		x->v[i] = x->v[0] + a_n * i;
	x->m = a_m;
	x->n = a_n;
	for (i = 0; i < a_m; i++){
		for (j = 0; j < a_n; j++){
			x->v[i][j] = A[i][j];
		}
	}

	/* householder */
	mat q[x->m];
	mat z = x;
	mat z1;
	int minor_z1_depth = a_m;
	int k,i;
	for (k = 0; k < a_m - 1; k++) {
		double e[x->m], x[x->m], a;
		minor_z1_depth = k;
		/* generate a minor matrix z1 */
		z1 = (mat) malloc (sizeof(mat_t));
		z1->v = (double**) malloc (sizeof(double) * z->m);
		z1->v[0] = (double*) calloc (sizeof(double), z->m * z->n);
		z1->m = z->m;
		z1->n = z->n;
/*
		for (i = 0; i < minor_z1_depth; i++){
			z1->v[i] = z1->v[0] + z->n * i; 
		}	
		for (i = 0; i < minor_z1_depth; i++){
			z1->v[i][i] = 1;
		}
/*
		for (i = minor_z1_depth; i < a_m; i++){
			for (j = minor_z1_depth; j < z->n; j++){
				z1->v[i][j] = z->v[i][j];
			}
		}*/
		/* ****************************** */ 
	}

	return 0;
}

