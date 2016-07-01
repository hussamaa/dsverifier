#!/bin/bash
#
# DSVerifier - Script Results Extractor
#
#               Universidade Federal do Amazonas - UFAM
# Author:       Lennon Chaves <lennon.correach@gmail.com>
#
# ------------------------------------------------------
#
# Script to extract and separate according to realization: DFI, DFII and TDFII.
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

DFI=$(cat $OUTPUT_FILE | grep " DFI " | cut -d "=" -f2 );
DFII=$(cat $OUTPUT_FILE | grep " DFII " | cut -d "=" -f2 );
TDFII=$(cat $OUTPUT_FILE | grep " TDFII " | cut -d "=" -f2 );

echo $DFI "\n";
echo $DFII "\n";
echo $TDFII "\n";
