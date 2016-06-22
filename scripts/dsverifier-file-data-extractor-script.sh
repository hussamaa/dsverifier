#!/bin/bash
#
# DSVerifier - Script Results Extractor
#
#               Universidade Federal do Amazonas - UFAM
# Author:       Lennon Chaves <lennon.correach@gmail.com>
#
# ------------------------------------------------------
#
# Script to extract data from dsverifer
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

REALIZATION=$(cat $OUTPUT_FILE | grep " Realization \=" | cut -d "=" -f2 );
IMPLEMENTATION=$(cat $OUTPUT_FILE | grep " Implementation \=" | cut -d "=" -f2 | sed 's/<//' | sed 's/>//' | tr ',' ' ');
NUMERATOR=$(cat $OUTPUT_FILE | grep " Numerator  \=" | cut -d "=" -f2 | sed 's/}//' | sed 's/{//');
DENOMINATOR=$(cat $OUTPUT_FILE | grep " Denominator  \=" | cut -d "=" -f2 | sed 's/}//' | sed 's/{//');
INPUTS=$(cat $OUTPUT_FILE | grep " Inputs =" | cut -d "=" -f2 | sed 's/}//' | sed 's/{//');
INITIAL_STATES=$(cat $OUTPUT_FILE | grep " Initial States =" | cut -d "=" -f2 | sed 's/}//' | sed 's/{//');
COUNT=0;
INPUT_ITEM=0;

for inputs_item in $INPUTS; do
   INPUT_ITEM=$inputs_item;
   COUNT=$((COUNT + 1));
done

echo $REALIZATION " " $NUMERATOR " " $DENOMINATOR " " $INITIAL_STATES " " $INPUT_ITEM " " $IMPLEMENTATION " " $COUNT > extraction_item.out;
