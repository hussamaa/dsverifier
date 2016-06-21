#!/bin/bash
#
# DSVerifier - Script Results Extractor
#
#               Universidade Federal do Amazonas - UFAM
# Author:       Lennon Chaves <lennon.correach@gmail.com>
#
# ------------------------------------------------------
#
# Script to extract outputs from dsverifer
# 
# Usage Example:
# $ sh script file.out
#
# ------------------------------------------------------

OUTPUT_FILE=$1;

if [ -z OUTPUT_FILE ]; then
	echo "Inform a file for extract the results (use: $0 \$PATH)";
	exit 1;
fi

INPUTS_=$(cat $OUTPUT_FILE | grep " plant_cbmc.a\[" | cut -d " " -f3 | cut -d "=" -f2);
OUTPUTS_=$(cat $OUTPUT_FILE | grep " plant_cbmc.b\[" | cut -d " " -f3 | cut -d "=" -f2);
INITIAL_STATES_DFI_=$(cat $OUTPUT_FILE | grep "y0\["  | cut -d " " -f3 | cut -d "=" -f2);
INITIAL_STATES_DFII_TDFII_=$(cat $OUTPUT_FILE | grep "w0\["  | cut -d " " -f3 | cut -d "=" -f2);

echo $INPUTS_;
echo $OUTPUTS_;
echo $INITIAL_STATES_DFI_;
echo $INITIAL_STATES_DFII_TDFII_;

#while read -r line
#do
#    name="$line"
#    echo "Name read from file - $name"
#done < "$OUTPUT_FILE"

