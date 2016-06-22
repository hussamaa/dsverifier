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
EXTRACTION="";

for file_desired in $RESULT; do

OUTPUT_FILE=$file_desired;

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

SPACE=" ";
ENTER="\n";
ITEM=$REALIZATION$SPACE$NUMERATOR$SPACE$DENOMINATOR$SPACE$INITIAL_STATES$SPACE$INPUT_ITEM$SPACE$IMPLEMENTATION$SPACE$COUNT$ENTER;

EXTRACTION="$EXTRACTION $ITEM";

done


echo $EXTRACTION > extraction_data.out;
