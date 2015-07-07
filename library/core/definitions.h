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
 * definitions file
 *
 * ------------------------------------------------------
*/

#include <stdlib.h>
#include <assert.h>

/* realizations (use: -DREALIZATION=DIRECTFORMI) */
#define DIRECTFORMI							1
#define DIRECTFORMII						2
#define TRANSPOSEDDIRECTFORMII				3
#define DELTADIRECTFORMI					4
#define DELTADIRECTFORMII					5
#define DELTATRANSPOSEDDIRECTFORMII			6
#define DIRECTFORMICASCADE   				7
#define DIRECTFORMIICASCADE   				8
#define TRANSPOSEDDIRECTFORMIICASCADE   	9
#define DELTADIRECTFORMICASCADE   			10
#define DELTADIRECTFORMIICASCADE   			11
#define DELTATRANSPOSEDDIRECTFORMIICASCADE 	12

/* nickname for realizations (use: -DREALIZATION=DFI) */
#define DFI									1
#define DFII								2
#define TDFII								3
#define DDFI            					4
#define DDFII								5
#define TDDFII								6
#define CDFI            					7
#define CDFII								8
#define CTDFII								9
#define CDDFI            					10
#define CDDFII								11
#define CTDDFII								12

/* property verification (use: -DPROPERTY=OVERFLOW) */
#define NOTHING 							0
#define OVERFLOW 							1
#define ZERO_INPUT_LIMIT_CYCLE				2
#define LIMIT_CYCLE 						3
#define TIMING 								4
#define ERROR								5
#define STABILITY 							6
#define MINIMUM_PHASE 						7
#define STABILITY_CLOSED_LOOP				8
#define LIMIT_CYCLE_CLOSED_LOOP				9

/** Check Required Parameters */
#ifndef PROPERTY
	#define PROPERTY 				0
#endif
#ifndef REALIZATION
	#define REALIZATION 			0
#endif
#ifndef X_SIZE
	#define X_SIZE 					0
#endif
#ifndef EXPECTED_ERROR
	#define EXPECTED_ERROR 			-1
#endif

/* processor parameters (OBSOLETE) */
#define CLOCK								16000000
#define CYCLE								1 / CLOCK
#ifndef SAMPLERATE
	#define SAMPLERATE 						100
#endif
#define DEADLINE 							1 / SAMPLERATE
#define OVERHEAD							0

/* overflow and x_size parameters */
int X_SIZE_VALUE = 0;
int OVERFLOW_MODE = 1; 						/* DETECT_OVERFLOW */

/* connection mode for control + model (use: -DCONNECTION_MODE=SERIES) */
#define SERIES 								1
#define FEEDBACK 							2
#ifndef CONNECTION_MODE
	#define CONNECTION_MODE					0
#endif

/* digital system structure */
typedef struct {
  double a[100];
  int a_size;
  double b[100];
  int b_size;
  double sample_time;
  double a_uncertainty[100];
  double b_uncertainty[100];
} digital_system;

/* implementation structure */
typedef struct {
   int int_bits;
   int frac_bits;
   double max;
   double min;
   int default_realization;
   double delta;
   int scale;
} implementation;
