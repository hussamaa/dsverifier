#include <stdio.h>
#include <stdlib.h>
#include <math.h>
 
typedef struct {
	int m, n;
	double ** v;
} mat_t, * mat;
 
mat matrix_new(int m, int n){
	mat x = (mat)malloc(sizeof(mat_t));
	x->v = (double**)malloc(sizeof(double) * m);
	x->v[0] = (double*)calloc(sizeof(double), m * n);
	int i;
	for (i = 0; i < m; i++)
		x->v[i] = x->v[0] + n * i;
	x->m = m;
	x->n = n;
	return x;
}
 
void matrix_delete(mat m){
	free(m->v[0]);
	free(m->v);
	free(m);
}
 
void matrix_transpose(mat m){
	int i,j;
	for (i = 0; i < m->m; i++) {
		for (j = 0; j < i; j++) {
			double t = m->v[i][j];
			m->v[i][j] = m->v[j][i];
			m->v[j][i] = t;
		}
	}
}
 
mat matrix_copy(void * a, int m, int n){
	mat x = matrix_new(m, n);
	int i,j;
	for (i = 0; i < m; i++)
		for (j = 0; j < n; j++)
			x->v[i][j] = ((double(*)[n])a)[i][j];
	return x;
}
 
mat matrix_mul(mat x, mat y) {
	if (x->n != y->m) return 0;
	mat r = matrix_new(x->m, y->n);
	int i, j, k;
	for (i = 0; i < x->m; i++)
		for (j = 0; j < y->n; j++)
			for (k = 0; k < x->n; k++)
				r->v[i][j] += x->v[i][k] * y->v[k][j];
	return r;
}
 
mat matrix_minor(mat x, int d) {
	mat m = matrix_new(x->m, x->n);
	int i, j;
	for (i = 0; i < d; i++)
		m->v[i][i] = 1;
	for (i = d; i < x->m; i++)
		for (j = d; j < x->n; j++)
			m->v[i][j] = x->v[i][j];
	return m;
}
 
/* c = a + b * s */
double * vmadd(double a[], double b[], double s, double c[], int n) {
	int i;
	for (i = 0; i < n; i++)
		c[i] = a[i] + s * b[i];
	return c;
}
 
/* m = I - v v^T */
mat vmul(double v[], int n){
	mat x = matrix_new(n, n);
	int i, j;
	for (i = 0; i < n; i++)
		for (j = 0; j < n; j++)
			x->v[i][j] = -2 *  v[i] * v[j];
	for (i = 0; i < n; i++)
		x->v[i][i] += 1;
 
	return x;
}
 
/* ||x|| */
double vnorm(double x[], int n){
	double sum = 0;
	int i;
	for (i = 0; i < n; i++) sum += x[i] * x[i];
	return sqrt(sum);
}
 
/* y = x / d */
double* vdiv(double x[], double d, double y[], int n){
	int i;
	for (i = 0; i < n; i++) y[i] = x[i] / d;
	return y;
}
 
/* take c-th column of m, put in v */
double * mcol(mat m, double *v, int c){
	int i;
	for (i = 0; i < m->m; i++)
		v[i] = m->v[i][c];
	return v;
}
 
void matrix_show(mat m){
	int i, j;
	for(i = 0; i < m->m; i++) {
		for (j = 0; j < m->n; j++) {
			printf("  %5.3f", m->v[i][j]);
		}
		printf("\n");
	}
	printf("\n");
}
 
void householder(mat m, mat *R, mat *Q){
	mat q[m->m];
	mat z = m, z1;
	int k,i;
	for (k = 0; k < m->m - 1; k++) {
		double e[m->m], x[m->m], a;
		z1 = matrix_minor(z, k);
		if (z != m) matrix_delete(z);
		z = z1;
 
		mcol(z, x, k);
		a = vnorm(x, m->m);
		if (m->v[k][k] > 0) a = -a;
 
		for (i = 0; i < m->m; i++)
			e[i] = (i == k) ? 1 : 0;
 
		vmadd(x, e, a, e, m->m);
		vdiv(e, vnorm(e, m->m), e, m->m);
		q[k] = vmul(e, m->m);
		z1 = matrix_mul(q[k], z);
		if (z != m) matrix_delete(z);
		z = z1;
	}
	matrix_delete(z);
	*Q = q[0];
	*R = matrix_mul(q[0], m);
	for (i = 1; i < m->m - 1; i++) {
		z1 = matrix_mul(q[i], *Q);
		if (i > 1) matrix_delete(*Q);
		*Q = z1;
		matrix_delete(q[i]);
	}
	matrix_delete(q[0]);
	z = matrix_mul(*Q, m);
	matrix_delete(*R);
	*R = z;
	matrix_transpose(*Q);
}
 
double in[][3] = {
	{ 1, 1, -1 },
	{ 1, 2,  1 },
	{ 1, 2,  1 },
};
 
int main()
{
	mat R, Q;
	mat x = matrix_copy(in, 3, 3);
	householder(x, &R, &Q);
 
	printf("Q\n"); matrix_show(Q);
	printf("R\n"); matrix_show(R);
 
	matrix_delete(x);
	matrix_delete(R);
	matrix_delete(Q);	
	return 0;
}
