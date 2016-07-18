#!/bin/bash
#
# DSVerifier - Script Results Extractor
#
#               Universidade Federal do Amazonas - UFAM
# Author:       Lennon Chaves <lennon.correach@gmail.com>
#
# ------------------------------------------------------
#
# Script to extract data from dsverifer considering the PATH
# 
# Usage Example:
# $ sh script $PATH
#
# ------------------------------------------------------


if [ -z "$1" ]; then
	echo "Inform a directory for extract the results (use: $0 \$PATH)";
	exit 1;
fi

PREVIOUS_FOLDER=$(pwd);
DESIRED_FOLDER=$1;

if [ ! -d "$DESIRED_FOLDER" ]; then
	"The directory $DESIRED_FOLDER doesn't exists";
	exit 1;
fi

cd $DESIRED_FOLDER;

FILES=$(ls -tr $(pwd) | grep out);
FOLDER=${PWD##*/}
RESULT="*.out";
EXTRACTION="\n";

for file_desired in $RESULT; do
	
OUTPUT_FILE=$file_desired;
OUT=$(cat $OUTPUT_FILE);

VERIFICATION_FAILED=$(echo "$OUT" | grep "FAILED" | wc -l);

if [ $VERIFICATION_FAILED -eq 1 ]; then

REALIZATION=$(cat $OUTPUT_FILE | grep " Realization \=" | cut -d "=" -f2 );
IMPLEMENTATION=$(cat $OUTPUT_FILE | grep " Implementation \=" | cut -d "=" -f2 | sed 's/<//' | sed 's/>//' | tr ',' ' ');
NUMERATOR=$(cat $OUTPUT_FILE | grep "Numerator (fixed-point) \=" | cut -d "=" -f2 | sed 's/}//' | sed 's/{//');
DENOMINATOR=$(cat $OUTPUT_FILE | grep "Denominator (fixed-point) \=" | cut -d "=" -f2 | sed 's/}//' | sed 's/{//');
INPUTS=$(cat $OUTPUT_FILE | grep " Inputs =" | cut -d "=" -f2 | sed 's/}//' | sed 's/{//');
INITIAL_STATES=$(cat $OUTPUT_FILE | grep " Initial States =" | cut -d "=" -f2 | sed 's/}//' | sed 's/{//');
COUNT=0;
ORDER=0;
INPUT_ITEM=0;

for inputs_item in $INPUTS; do
   INPUT_ITEM=$inputs_item;
   COUNT=$((COUNT + 1));
done

for parameter_item in $NUMERATOR; do
   ORDER=$((ORDER + 1));
done

SPACE=" ";
ENTER="\n";
ZERO="0";

if [ $ORDER = 2 ]; then
ITEM=$REALIZATION$SPACE$OUTPUT_FILE$SPACE$IMPLEMENTATION$SPACE$COUNT$SPACE$ORDER$NUMERATOR$ZERO$SPACE$DENOMINATOR$ZERO$SPACE$INITIAL_STATES$ZERO$SPACE$INPUT_ITEM$SPACE$ENTER;
else
ITEM=$REALIZATION$SPACE$OUTPUT_FILE$SPACE$IMPLEMENTATION$SPACE$COUNT$SPACE$ORDER$NUMERATOR$SPACE$DENOMINATOR$SPACE$INITIAL_STATES$SPACE$INPUT_ITEM$SPACE$ENTER;
fi

EXTRACTION="$EXTRACTION $ITEM";

fi

done


echo $EXTRACTION > dsv_counterexample_parameters.txt;
