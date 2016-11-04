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

extern digital_system ds;
extern hardware hw;
extern int generic_timer;

/*function to saturate node in case of overflow verification*/
fxp_t saturate_node(fxp_t node){

fxp_t node_saturated = node;

 if((overflow_mode == SATURATE)&& (PROPERTY == OVERFLOW))
   {
     node_saturated = fxp_quantize(node);
   }

return node_saturated;

}

/*function to refresh from saturate overflow mode to detect overflow mode, in case of overflow verification*/
void refresh_overflow_mode()
{
 if ((overflow_mode == SATURATE) && (PROPERTY == OVERFLOW))
   {
     overflow_mode = DETECT_OVERFLOW;
   }
}

/** direct form I realization in fixed point */
fxp_t fxp_direct_form_1(fxp_t y[], fxp_t x[], fxp_t a[], fxp_t b[], int Na,	int Nb) {
	fxp_t *a_ptr, *y_ptr, *b_ptr, *x_ptr;
	fxp_t sum = 0;
	a_ptr = &a[1];
	y_ptr = &y[Na - 1];
	b_ptr = &b[0];
	x_ptr = &x[Nb - 1];
	int i, j;
	for (i = 0; i < Nb; i++) {
		sum = fxp_add(sum, fxp_mult(*b_ptr++, *x_ptr--));
	}
	sum = saturate_node(sum);
	refresh_overflow_mode();

	for (j = 1; j < Na; j++) {
		sum = fxp_sub(sum, fxp_mult(*a_ptr++, *y_ptr--));
	}
	sum = fxp_div(sum,a[0]);
	return fxp_quantize(sum);
}

/** direct form II realization in fixed point */
fxp_t fxp_direct_form_2(fxp_t w[], fxp_t x, fxp_t a[], fxp_t b[], int Na,	int Nb) {
	fxp_t *a_ptr, *b_ptr, *w_ptr;
	fxp_t sum = 0;
	a_ptr = &a[1];
	b_ptr = &b[0];
	w_ptr = &w[1];
	int k, j;
	for (j = 1; j < Na; j++) {
		w[0] = fxp_sub(w[0], fxp_mult(*a_ptr++, *w_ptr++));
	}
	w[0] = fxp_add(w[0], x); //w[0] += x;
	w[0] = fxp_div(w[0], a[0]);
	
	w[0] = saturate_node(w[0]);
	refresh_overflow_mode();

	w_ptr = &w[0];
	for (k = 0; k < Nb; k++) {
		sum = fxp_add(sum, fxp_mult(*b_ptr++, *w_ptr++));
	}
	return fxp_quantize(sum);
}

/** transposed direct form II realization in fixed point */
fxp_t fxp_transposed_direct_form_2(fxp_t w[], fxp_t x, fxp_t a[], fxp_t b[], int Na, int Nb) {
	fxp_t *a_ptr, *b_ptr;
	fxp_t yout = 0;
	a_ptr = &a[1];
	b_ptr = &b[0];
	int Nw = Na > Nb ? Na : Nb;
	yout = fxp_add(fxp_mult(*b_ptr++, x), w[0]);
	yout = fxp_div(yout, a[0]);
	int j;
	for (j = 0; j < Nw - 1; j++) {
		w[j] = w[j + 1];
		if (j < Na - 1) {
			w[j] = fxp_sub(w[j], fxp_mult(*a_ptr++, yout));
		}
		if (j < Nb - 1) {
			w[j] = fxp_add(w[j], fxp_mult(*b_ptr++, x));
		}

	w[j] = saturate_node(w[j]);

	}
	
	refresh_overflow_mode();

	return fxp_quantize(yout);
}

/** direct form I realization using double precision */
double double_direct_form_1(double y[], double x[], double a[], double b[], int Na, int Nb) {
	double *a_ptr, *y_ptr, *b_ptr, *x_ptr;
	double sum = 0;
	a_ptr = &a[1];
	y_ptr = &y[Na - 1];
	b_ptr = &b[0];
	x_ptr = &x[Nb - 1];
	int i, j;
	for (i = 0; i < Nb; i++) {
		sum += *b_ptr++ * *x_ptr--;
	}
	for (j = 1; j < Na; j++) {
		sum -= *a_ptr++ * *y_ptr--;
	}
	sum = (sum / a[0]);
	return sum;
}

/** direct form II realization using double precision */
double double_direct_form_2(double w[], double x, double a[], double b[], int Na, int Nb) {
	double *a_ptr, *b_ptr, *w_ptr;
	double sum = 0;
	a_ptr = &a[1];
	b_ptr = &b[0];
	w_ptr = &w[1];
	int k, j;
	for (j = 1; j < Na; j++) {
		w[0] -= *a_ptr++ * *w_ptr++;
	}
	w[0] += x;
	w[0] = w[0] / a[0];
	w_ptr = &w[0];
	for (k = 0; k < Nb; k++) {
		sum += *b_ptr++ * *w_ptr++;
	}
	return sum;
}

/** transposed direct form II realization using double precision */
double double_transposed_direct_form_2(double w[], double x, double a[], double b[], int Na, int Nb) {
	double *a_ptr, *b_ptr;
	double yout = 0;
	a_ptr = &a[1];
	b_ptr = &b[0];
	int Nw = Na > Nb ? Na : Nb;
	yout = (*b_ptr++ * x) + w[0];
	yout = yout / a[0];
	int j;
	for (j = 0; j < Nw - 1; j++) {
		w[j] = w[j + 1];
		if (j < Na - 1) {
			w[j] -= *a_ptr++ * yout;
		}
		if (j < Nb - 1) {
			w[j] += *b_ptr++ * x;
		}
	}
	return yout;
}

/** direct form I realization using float precision */
float float_direct_form_1(float y[], float x[], float a[], float b[], int Na, int Nb) {
	float *a_ptr, *y_ptr, *b_ptr, *x_ptr;
	float sum = 0;
	a_ptr = &a[1];
	y_ptr = &y[Na - 1];
	b_ptr = &b[0];
	x_ptr = &x[Nb - 1];
	int i, j;
	for (i = 0; i < Nb; i++) {
		sum += *b_ptr++ * *x_ptr--;
	}
	for (j = 1; j < Na; j++) {
		sum -= *a_ptr++ * *y_ptr--;
	}
	sum = (sum / a[0]);
	return sum;
}

/** direct form II realization using float precision */
float float_direct_form_2(float w[], float x, float a[], float b[], int Na, int Nb) {
	float *a_ptr, *b_ptr, *w_ptr;
	float sum = 0;
	a_ptr = &a[1];
	b_ptr = &b[0];
	w_ptr = &w[1];
	int k, j;
	for (j = 1; j < Na; j++) {
		w[0] -= *a_ptr++ * *w_ptr++;
	}
	w[0] += x;
	w[0] = w[0] / a[0];
	w_ptr = &w[0];
	for (k = 0; k < Nb; k++) {
		sum += *b_ptr++ * *w_ptr++;
	}
	return sum;
}

/** transposed direct form II realization using float precision */
float float_transposed_direct_form_2(float w[], float x, float a[], float b[], int Na, int Nb) {
	float *a_ptr, *b_ptr;
	float yout = 0;
	a_ptr = &a[1];
	b_ptr = &b[0];
	int Nw = Na > Nb ? Na : Nb;
	yout = (*b_ptr++ * x) + w[0];
	yout = yout / a[0];
	int j;
	for (j = 0; j < Nw - 1; j++) {
		w[j] = w[j + 1];
		if (j < Na - 1) {
			w[j] -= *a_ptr++ * yout;
		}
		if (j < Nb - 1) {
			w[j] += *b_ptr++ * x;
		}
	}
	return yout;
}

/* direct form I realization using double precision and WCET analysis of assembly code generated by MSP430 CCS compiler */
double double_direct_form_1_MSP430(double y[], double x[], double a[], double b[], int Na, int Nb){
	/* timer1 += 40; */
	int timer1 = OVERHEAD;
	double *a_ptr, *y_ptr, *b_ptr, *x_ptr;									/* timer1 += 8;  */
	double sum = 0;															/* timer1 += 4;  */
	a_ptr = &a[1];															/* timer1 += 2;  */
	y_ptr = &y[Na-1];														/* timer1 += 13; */
	b_ptr = &b[0];															/* timer1 += 1;  */
	x_ptr = &x[Nb-1];														/* timer1 += 13; */
	int i, j;																/* timer1 += 1;  */
	timer1 += 91;		/* (40+42+9) */
	for (i = 0; i < Nb; i++){												/* timer1 += 9;  */
		sum += *b_ptr++ * *x_ptr--;											/* timer1 += 35  */
		timer1 += 47;	/* (12+35);  */
	}																		/* timer1 += 12; */
	for (j = 1; j < Na; j++){												/* timer1 += 3;  */
		sum -= *a_ptr++ * *y_ptr--;											/* timer1 += 37; */
		timer1 += 57;	/* (37+20);  */
	}																		/* timer1 += 20; */
	timer1 += 3;		/* (3+7);    */
	assert((double) timer1 * hw.cycle <= ds.sample_time);
	return sum;																/* timer1 += 7;  */
}

/* direct form 2 realization using double precision and WCET analysis of assembly code generated by MSP430 CCS compiler */
double double_direct_form_2_MSP430(double w[], double x, double a[], double b[], int Na, int Nb) {
	/* timer1 += 40; */
	int timer1 = OVERHEAD;
	double *a_ptr, *b_ptr, *w_ptr;											/* timer1 += 7;  */
	double sum = 0;															/* timer1 += 4;  */
	a_ptr = &a[1];															/* timer1 += 7;  */
	b_ptr = &b[0];
	w_ptr = &w[1];															/* timer1 += 2;  */
	int k, j;																/* timer1 += 2;  */
	timer1 += 71;	/* (40+22+9) */
	for (j = 1; j < Na; j++) {												/* timer1 += 9;  */
		w[0] -= *a_ptr++ * *w_ptr++;										/* timer1 += 42; */
		timer1 += 54;	/* (42+12) */
	}																		/* timer1 += 12; */
	w[0] += x;
	w[0] = w[0] / a[0];/* timer1 += 21; */
	w_ptr = &w[0];															/* timer1 += 1;  */
	for (k = 0; k < Nb; k++) {												/* timer1 += 9;  */
		sum += *b_ptr++ * *w_ptr++;											/* timer1 += 34; */
		timer1 += 46;	/* (34+12) */
	}																		/* timer1 += 12; */
	timer1 += 38;	/* (21+1+9+7) */
	assert((double) timer1 * hw.cycle <= ds.sample_time);
	return sum;																/* timer1 += 7;  */
}

/* transposed direct form 2 realization using double precision and WCET analysis of assembly code generated by MSP430 CCS compiler */
double double_transposed_direct_form_2_MSP430(double w[], double x, double a[], double b[], int Na, int Nb) {
	/* timer1 += 40; */
	int timer1 = OVERHEAD;
	double *a_ptr, *b_ptr;													/* timer1 += 6;  */
	double yout = 0;														/* timer1 += 3;  */
	a_ptr = &a[1];															/* timer1 += 7;  */
	b_ptr = &b[0];
	int Nw = Na > Nb ? Na : Nb;												/* timer1 += 10; */
	yout = (*b_ptr++ * x) + w[0];											/* timer1 += 36; */
	int j;
	timer1 += 105;	/* (40+62+3) */
	for (j = 0; j < Nw - 1; j++) {											/* timer1 += 3;  */
		w[j] = w[j + 1];													/* timer1 += 12; */
		if (j < Na - 1) {													/* timer1 += 9;  */
			w[j] -= *a_ptr++ * yout;										/* timer1 += 34; */
			timer1 += 41;	/* (34+7) */
		}																	/* timer1 += 7;  */
		if (j < Nb - 1) {													/* timer1 += 13; */
			w[j] += *b_ptr++ * x;											/* timer1 += 38; */
			timer1 += 38;	/* (38) */
		}
		timer1 += 54;	/* (12+9+13+20) */
	}																		/* timer1 += 20; */
	timer1 += 7;	/* (7) */
	assert((double) timer1 * hw.cycle <= ds.sample_time);
	return yout;															/* timer1 += 7;  */
}

/* direct form I realization using double precision and WCET analysis of assembly code generated by an generic compiler */
double generic_timing_double_direct_form_1(double y[], double x[], double a[], double b[], int Na, int Nb){
	generic_timer += ((6 * hw.assembly.push) + (3 * hw.assembly.in) + (1 * hw.assembly.sbiw) + (1 * hw.assembly.cli) + (3 * hw.assembly.out) + (12 * hw.assembly.std));
	double *a_ptr, *y_ptr, *b_ptr, *x_ptr;
	double sum = 0;
	a_ptr = &a[1];
	y_ptr = &y[Na-1];
	b_ptr = &b[0];
	x_ptr = &x[Nb-1];
	generic_timer += ((12 * hw.assembly.std) + (12 * hw.assembly.ldd) + (2 * hw.assembly.subi) + (2 * hw.assembly.sbci) + (4 * hw.assembly.lsl) + (4 * hw.assembly.rol) + (2 * hw.assembly.add) + (2 * hw.assembly.adc) + (1 * hw.assembly.adiw));
	int i, j;
	generic_timer += ((2 * hw.assembly.std) + (1 * hw.assembly.rjmp));
	for (i = 0; i < Nb; i++){
		generic_timer += ((20 * hw.assembly.ldd) + (24 * hw.assembly.mov) + (2 * hw.assembly.subi) + (1 * hw.assembly.sbci) + (1 * hw.assembly.sbc) + (10 * hw.assembly.std) + (2 * hw.assembly.ld) + (2 * hw.assembly.rcall) + (1 * hw.assembly.adiw) + (1 * hw.assembly.cp) + (1 * hw.assembly.cpc) + (1 * hw.assembly.adiw) + (1 * hw.assembly.brge) + (1 * hw.assembly.rjmp));
		sum += *b_ptr++ * *x_ptr--;
	}
	generic_timer += ((2 * hw.assembly.ldi) + (2 * hw.assembly.std) + (1 * hw.assembly.rjmp));
	for (j = 1; j < Na; j++){
		generic_timer += ((22 * hw.assembly.ldd) + (24 * hw.assembly.mov) + (2 * hw.assembly.subi) + (8 * hw.assembly.std) + (1 * hw.assembly.sbci) + (2 * hw.assembly.ld) + (2 * hw.assembly.rcall) + (1 * hw.assembly.sbc) + (1 * hw.assembly.adiw) + (1 * hw.assembly.cp) + (1 * hw.assembly.cpc) + (1 * hw.assembly.adiw) + (1 * hw.assembly.brge) + (1 * hw.assembly.rjmp));
		sum -= *a_ptr++ * *y_ptr--;
	}
	generic_timer += ((4 * hw.assembly.ldd) + (4 * hw.assembly.mov) + (1 * hw.assembly.adiw) + (1 * hw.assembly.in) + (1 * hw.assembly.cli) + (3 * hw.assembly.out) + (6 * hw.assembly.pop) + (1 * hw.assembly.ret));
	return sum;
}

/* direct form 2 realization using double precision and WCET analysis of assembly code generated by an generic compiler */
double generic_timing_double_direct_form_2(double w[], double x, double a[], double b[], int Na, int Nb) {
	generic_timer += ((8 * hw.assembly.push) + (14 * hw.assembly.std) + (3 * hw.assembly.out) + (3 * hw.assembly.in) + (1 * hw.assembly.sbiw) + (1 * hw.assembly.cli));
	double *a_ptr, *b_ptr, *w_ptr;
	double sum = 0;
	a_ptr = &a[1];
	b_ptr = &b[0];
	w_ptr = &w[1];
	int k, j;
	generic_timer += ((10 * hw.assembly.std) + (6 * hw.assembly.ldd) + (2 * hw.assembly.adiw));
	generic_timer += ((2 * hw.assembly.ldi) + (2 * hw.assembly.std) + (1 * hw.assembly.rjmp));
	for (j = 1; j < Na; j++) {
		w[0] -= *a_ptr++ * *w_ptr++;
		generic_timer += ((23 * hw.assembly.ldd) + (32 * hw.assembly.mov) + (9 * hw.assembly.std) + (2 * hw.assembly.subi) + (3 * hw.assembly.ld) + (2 * hw.assembly.rcall) + (2 * hw.assembly.sbci) + (1 * hw.assembly.st) + (1 * hw.assembly.adiw) + (1 * hw.assembly.cp) + (1 * hw.assembly.cpc) + (1 * hw.assembly.brge));
	}
	w[0] += x;
	w_ptr = &w[0];
	generic_timer += ((13 * hw.assembly.ldd) + (12 * hw.assembly.mov) + (5 * hw.assembly.std) + (1 * hw.assembly.st) + (1 * hw.assembly.ld) + (1 * hw.assembly.rcall));
	generic_timer += ((2 * hw.assembly.std) + (1 * hw.assembly.rjmp));
	for (k = 0; k < Nb; k++) {
		sum += *b_ptr++ * *w_ptr++;
		generic_timer += ((20 * hw.assembly.ldd) + (24 * hw.assembly.mov) + (10 * hw.assembly.std) + (2 * hw.assembly.rcall) + (2 * hw.assembly.ld) + (2 * hw.assembly.subi) + (2 * hw.assembly.sbci) + (1 * hw.assembly.adiw) + (1 * hw.assembly.cp) + (1 * hw.assembly.cpc) + (1 * hw.assembly.brge) + (1 * hw.assembly.rjmp));
	}
	generic_timer += ((4 * hw.assembly.ldd) + (4 * hw.assembly.mov) + (1 * hw.assembly.adiw) + (1 * hw.assembly.in) + (1 * hw.assembly.cli) + (3 * hw.assembly.out) + (8 * hw.assembly.pop) + (1 * hw.assembly.ret));
	return sum;
}

/* transposed direct form 2 realization using double precision and WCET analysis of assembly code generated by an generic compiler */
double generic_timing_double_transposed_direct_form_2(double w[], double x, double a[], double b[], int Na, int Nb) {
	generic_timer += ((8 * hw.assembly.push) + (14 * hw.assembly.std) + (3 * hw.assembly.out) + (3 * hw.assembly.in) + (1 * hw.assembly.sbiw) + (1 * hw.assembly.cli));
	double *a_ptr, *b_ptr;
	double yout = 0;
	a_ptr = &a[1];
	b_ptr = &b[0];
	int Nw = Na > Nb ? Na : Nb;
	yout = (*b_ptr++ * x) + w[0];
	int j;
	generic_timer += ((15 * hw.assembly.std) + (22 * hw.assembly.ldd) + (24 * hw.assembly.mov) + (2 * hw.assembly.rcall) + (2 * hw.assembly.ld) + (1 * hw.assembly.cp) + (1 * hw.assembly.cpc) + (1 * hw.assembly.subi) + (1 * hw.assembly.sbci) + (1 * hw.assembly.brge) + (1 * hw.assembly.adiw));
	generic_timer += ((2 * hw.assembly.std) + (1 * hw.assembly.rjmp));
	for (j = 0; j < Nw - 1; j++) {
		w[j] = w[j + 1];
		if (j < Na - 1) {
			w[j] -= *a_ptr++ * yout;
		}
		if (j < Nb - 1) {
			w[j] += *b_ptr++ * x;
		}
		generic_timer += ((70 * hw.assembly.mov) + (65 * hw.assembly.ldd) + (12 * hw.assembly.lsl) + (12 * hw.assembly.rol) + (15 * hw.assembly.std) + (6 * hw.assembly.add) + (6 * hw.assembly.adc) + (2 * hw.assembly.adiw) + (3 * hw.assembly.cpc) + (3 * hw.assembly.cp) + (5 * hw.assembly.ld) + (4 * hw.assembly.rcall) + (5 * hw.assembly.subi) + (3 * hw.assembly.rjmp) + (2 * hw.assembly.brlt) + (3 * hw.assembly.st) + (2 * hw.assembly.sbci) + (3 * hw.assembly.sbc) + (1 * hw.assembly.brge));
	}
	generic_timer += ((4 * hw.assembly.ldd) + (4 * hw.assembly.mov) + (8 * hw.assembly.pop) + (3 * hw.assembly.out) + (1 * hw.assembly.in) + (1 * hw.assembly.cli) + (1 * hw.assembly.adiw) + (1 * hw.assembly.ret));
	return yout;
}

/** direct form 1 realization (implementation 2) */
void double_direct_form_1_impl2(double x[], int x_size, double b[], int b_size, double a[], int a_size, double y[]){
   int i = 0; int j = 0;
   /* system 1 h1(z) */
   double v[x_size];
   for(i = 0; i < x_size; i++){
      v[i] = 0;
      for(j = 0; j < b_size; j++){
         if (j > i) break;
            v[i] = v[i] + x[i-j] * b[j];
         }
      }
   /* system 2 h2(z) */
   y[0] = v[0];
   for(i = 1; i < x_size; i++){
      y[i] = 0;
      y[i] = y[i] + v[i];
      for(j = 1; j < a_size; j++){
    	  if (j > i) break;
    	  y[i] = y[i] + y[i-j] * ((-1) * a[j]);
      }
   }
}

/** fixed point direct form 1 realization (implementation 2) */
void fxp_direct_form_1_impl2(fxp_t x[], int x_size, fxp_t b[], int b_size, fxp_t a[], int a_size, fxp_t y[]){
   int i = 0; int j = 0;
   /* system 1 h1(z) */
   fxp_t v[x_size];
   for(i = 0; i < x_size; i++){
      v[i] = 0;
      for(j = 0; j < b_size; j++){
         if (j > i) break;
         v[i] = fxp_add(v[i], fxp_mult(x[i-j], b[j]));
      }
   }

   /* system 2 h2(z) */
   y[0] = v[0];
   for(i = 1; i < x_size; i++){
	   y[i] = 0;
	   y[i] = fxp_add(y[i], v[i]);
	   for(j = 1; j < a_size; j++){
		   if (j > i) break;
		   y[i] = fxp_add(y[i], fxp_mult(y[i-j] , -a[j]));
	   }
   }
}
