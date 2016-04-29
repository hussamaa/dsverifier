#!/bin/bash
#
# DSVerifier - Benchmark Data Extractor
#
#               Universidade Federal do Amazonas - UFAM
# Author:       Hussama Ismail <hussamaismail@gmail.com>
#
# ------------------------------------------------------
#
# Script for extract data (input, states, and outputs)
# from benchmarks.
#
# Usage Example:
# $ sh script benchmarks_output_file
#
# ------------------------------------------------------

if [ -z "$1" ]; then
	echo "Inform a file for extract the results (use: $0 \$PATH)";
	exit 1;
fi

DESIRED_FILE=$1;
CURRENT_FRAC_BITS=12;

MODEL_CHECKER="CBMC"

SCALING_FACTOR=$((2**$CURRENT_FRAC_BITS));
INPUTS_FXP=$(cat $DESIRED_FILE | grep " x\[" | cut -d " " -f3 | cut -d "=" -f2);
OUTPUTS_FXP=$(cat $DESIRED_FILE | grep " y\[" | cut -d " " -f3 | cut -d "=" -f2);
INITIAL_STATES_DFI_FXP=$(cat $DESIRED_FILE | grep "y0\["  | cut -d " " -f3 | cut -d "=" -f2);
INITIAL_STATES_DFII_TDFII_FXP=$(cat $DESIRED_FILE | grep "w0\["  | cut -d " " -f3 | cut -d "=" -f2);

INPUTS=()
OUTPUTS=()
INITIAL_STATES=()

# getting inputs in floating point representation
for input_fxp in $INPUTS_FXP; do
   INPUTS+="$(echo $input_fxp/$SCALING_FACTOR | bc -l) ";
done

# getting outputs in floating point representation
for output_fxp in $OUTPUTS_FXP; do
   OUTPUTS+="$(echo $output_fxp/$SCALING_FACTOR | bc -l) ";
done

if [ -z "$INITIAL_STATES_DFII_TDFII_FXP" ]; then
  # get using DFI states
  for state_fxp in $INITIAL_STATES_DFI_FXP; do
     INITIAL_STATES+="$(echo $state_fxp/$SCALING_FACTOR | bc -l) ";
  done
else
  # get using DFII and DFII states
  for state_fxp in $INITIAL_STATES_DFII_TDFII_FXP; do
     INITIAL_STATES+="$(echo $state_fxp/$SCALING_FACTOR | bc -l) ";
  done
fi

echo "INITIAL_STATES: { ${INITIAL_STATES[@]} }"
echo "X: { ${INPUTS[@]} }"
echo "Y: { ${OUTPUTS[@]} }"
