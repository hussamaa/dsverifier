#!/bin/bash
#
# DSVerifier - Script Results Extractor
#
#               Universidade Federal do Amazonas - UFAM
# Author:       Lennon Chaves <lennon.correach@gmail.com>
#
# ------------------------------------------------------
#
# Script to extract only outputs from dsverifer considering the PATH
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
EXTRACTION="";

for file_desired in $RESULT; do

OUTPUT_FILE=$file_desired;

OUT=$(cat $OUTPUT_FILE);

VERIFICATION_FAILED=$(echo "$OUT" | grep "FAILED" | wc -l);

if [ $VERIFICATION_FAILED -eq 1 ]; then

OUTPUTS=$(cat $OUTPUT_FILE | grep " Outputs =" | cut -d "=" -f2 | sed 's/}//' | sed 's/{//');

SPACE=" ";
ENTER="\n";
ITEM=$OUTPUTS$ENTER;

EXTRACTION="$EXTRACTION $ITEM";

fi

done


echo $EXTRACTION > dsv_counterexamples_outputs.txt;
