#include <assert.h>

#ifndef _VERIFICATIONFXP_H

	#define _VERIFICATIONFXP_H	1

	#ifdef __cplusplus
		extern "C" {
		}
	#endif

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
	#define DIRECTFORMIPARALLEL					13
	#define DIRECTFORMIIPARALLEL				14
	#define TRANSPOSEDDIRECTFORMIIPARALLEL		15
	#define DELTADIRECTFORMIPARALLEL			16
	#define DELTADIRECTFORMIIPARALLEL			17
	#define DELTATRANSPOSEDDIRECTFORMIIPARALLEL	18

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
	#define LIMIT_CYCLE 						2
	#define TIMING 								3
	#define ERROR								4
	#define STABILITY 							5
    #define MINIMUM_PHASE 						6
	#define STABILITY_CLOSED_LOOP				7
	#define LIMIT_CYCLE_CLOSED_LOOP				8

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

#endif
