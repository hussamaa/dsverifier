#!/bin/bash
#
# DSVerifier - Script Results Extractor
#
#               Universidade Federal do Amazonas - UFAM
# Author:       Lennon Chaves <lennon.correach@gmail.com>
#
# ------------------------------------------------------
#
# Script to extract the results from verification using dsverifer considering the PATH
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

TOTAL_EXECUTIONS=0;
TOTAL_SUCCESS=0;
TOTAL_FAILS=0;
TOTAL_TIMEOUTS=0;

echo "";
echo "*** DETAILS BY FILE *** ";
echo "";

for file_desired in $RESULT; do

OUT_FILE=$file_desired;

# analyse the result 
OUT=$(cat $OUT_FILE);		

VERIFICATION_SUCCESSFUL=$(echo "$OUT" | grep "SUCCESSFUL" | wc -l); 
VERIFICATION_FAILED=$(echo "$OUT" | grep "FAILED" | wc -l);
VERIFICATION_TIMEOUT=$(echo "$OUT" | grep "Timed out" | wc -l);
TOTAL_EXECUTIONS=$((TOTAL_EXECUTIONS + 1));

if [ $VERIFICATION_SUCCESSFUL -eq 1 ]; then
   TOTAL_SUCCESS=$((TOTAL_SUCCESS + 1));
   echo "File: $OUT_FILE Result: $(echo -e "\033[0;32mSuccess\033[0m" | cut -d " " -f2)";       
elif [ $VERIFICATION_FAILED -eq 1 ]; then
   TOTAL_FAILS=$((TOTAL_FAILS + 1));
   echo "File: $OUT_FILE Result: $(echo -e "\\033[0;31mFail\033[0m" | cut -d " " -f2)";       
elif [ $VERIFICATION_TIMEOUT -eq 1 ]; then
   TOTAL_TIMEOUTS=$((TOTAL_TIMEOUTS + 1));
   echo "File: $OUT_FILE Result: $(echo -e "\\033[0;35mTimeout\033[0m" | cut -d " " -f2)";   
else 
   echo "File: $OUT_FILE Result: $(echo -e "\\033[0;33mUnknown\033[0m" | cut -d " " -f2)";   
fi

done

              
# show report
echo "";
echo "*** RESULTS *** ";
echo "Total of verifications: $TOTAL_EXECUTIONS";
echo "Total of success: $TOTAL_SUCCESS";
echo "Total of fails: $TOTAL_FAILS";
echo "Total of timeouts: $TOTAL_TIMEOUTS";
