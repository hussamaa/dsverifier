#include <assert.h>

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>

#define EPSILON 0.0001

int fatorial(int n);
float * binomio(int grau, float delta);
int coeficiente_binomial(int n, int p);
float * inverte_vetor(float * v, int n);
float * calcula_coeficientes_delta(float * vetor, int n, float delta);
void imprime_vetor(char * nome, float * v, int n);
void converte_ponteiro_vetor(float * v, float vr[], int n);
int compara_float(float a, float b);
double potencia (double a, double b);

void esbmc_binomio(int grau, float delta, float out[]);
void esbmc_calcula_coeficientes_delta(float vetor[], float out[], int n, float delta);
void esbmc_calcula_coeficientes_delta_b(float vetor[], float out[], int n, float delta);
void esbmc_inverte_vetor(float v[], float out[], int n);
void esbmc_inicia_vetor(float v[], int n);
int esbmc_check_stability(float a[], int n);

double potencia (double a, double b){
   int i;
   double acc = 1;
   for (i=0; i < b; i++){
	  acc = acc*a;
   }
   return acc;
}

int compara_float(float a, float b){
	float erro = fabs(a - b);
	if (erro < EPSILON){
		return 1;
	}else{
	return 0;
	}
}

void esbmc_inicia_vetor(float v[], int n){
   int i;
   for(i=0; i<n; i++){
	   v[i] = 0;
   }
}

void imprime_vetor(char * nome, float * v, int n){
   printf("%s = {", nome);
   int i;
   for(i=0; i < n; i++){
	  printf(" %f ", v[i]);
   }
   printf("}\n");
}

float * calcula_coeficientes_delta(float * vetor, int n, float delta){
   float * a_invertido = inverte_vetor(vetor, n);
   float * _a = malloc(sizeof(float) * n);
   int i,j;
   for(i=0; i < n; i++){
	  float * b = binomio(i, delta);
	  for(j=0; j<i+1; j++){
		 b[j] = b[j] * a_invertido[i];
		 _a[j] = _a[j] + b[j];
	  }
   }
   _a = inverte_vetor(_a, n);
   return _a;
}

void converte_ponteiro_vetor(float * v, float vr[], int n){
   float vetor[n];
   int i;
   for(i=0;i<n;i++){
	  vr[i] = v[i];
   }
}

float * inverte_vetor(float * v, int n){
   float * novo = malloc(sizeof(float) * (n));
   int i;
   for(i=0; i<n; i++){
	  novo[i] = v[n-i-1];
   }
   return novo;
}

float * binomio(int grau, float delta){
   float * v = malloc(sizeof(float) * (grau + 1));
   int i;
   for(i=0; i<=grau; i++){
	  v[grau-i] = coeficiente_binomial(grau, i) * pow(delta, grau-i);
   }
   return v;
}

int coeficiente_binomial(int n, int p){
   return fatorial(n) / (fatorial(p) * fatorial(n-p));
}

int fatorial(int n){
   return n == 0 ? 1 : n * fatorial(n-1);
}

void esbmc_binomio(int grau, float delta, float out[]){
   esbmc_inicia_vetor(out, 3);
   int i;
   for(i=0; i<=grau; i++){
	  out[grau-i] = coeficiente_binomial(grau, i) * potencia(delta, grau-i);
   }
}

void esbmc_inverte_vetor(float v[], float out[], int n){
   esbmc_inicia_vetor(out,n);
   int i;
   for(i=0; i<n; i++){
	  out[i] = v[n-i-1];
   }
}

void esbmc_calcula_coeficientes_delta(float vetor[], float out[], int n, float delta){
   esbmc_inicia_vetor(out,n);
   float a_invertido[n];
   esbmc_inicia_vetor(a_invertido,n);
   esbmc_inverte_vetor(vetor, a_invertido, n);
   float _a[n];
   esbmc_inicia_vetor(_a,n);
   int i,j;
   for(i=0; i < n; i++){
	  float b[n+1];
	  esbmc_inicia_vetor(b,n+1);
	  esbmc_binomio(i, delta, b);
	  for(j=0; j<i+1; j++){
		 b[j] = b[j] * a_invertido[i];
		 _a[j] = _a[j] + b[j];
	  }
   }
   esbmc_inverte_vetor(_a, out, n);
}

void esbmc_calcula_coeficientes_delta_b(float vetor[], float out[], int n, float delta){
   esbmc_inicia_vetor(out,n);
   float a_invertido[n];
   esbmc_inicia_vetor(a_invertido,n);
   esbmc_inverte_vetor(vetor, a_invertido, n);
   float _a[n];
   esbmc_inicia_vetor(_a,n);
   int i,j;
   for(i=0; i < n; i++){
	  float b[n+1];
	  esbmc_inicia_vetor(b,n+1);
	  esbmc_binomio(i, delta, b);
	  for(j=0; j<i+1; j++){
		 b[j] = b[j] * a_invertido[i];
		 _a[j] = _a[j] + b[j];
	  }
	  _a[i] = _a[i] / delta;
   }
   esbmc_inverte_vetor(_a, out, n);
}

int esbmc_check_stability(float a[], int n){
   int linhas = 2 * n - 1;
   int colunas = n;
   float m[linhas][n];
   int i,j;

   /* to put current values in stability counter-example
	* look for current_stability (use: --no-slice) */
   float current_stability[n];
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

int esbmc_check_stability_double(double a[], int n){
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

int esbmc_check_stability_double_closedloop(double a[], int n, double plant_num[], int p_num_size, double plant_den[], int p_den_size){
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
