#!/bin/bash
#
# DSVerifier - Benchmark Results Extractor
#
#               Universidade Federal do Amazonas - UFAM
# Author:       Hussama Ismail <hussamaismail@gmail.com>
#
# ------------------------------------------------------
#
# Script extract the benchmarks results
# 
# Usage Example:
# $ sh script benchmarks_output_folder
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
RESULT="out.txt";

CURRENT=-1;
LINE="";

DFI_SUCCESS=0;
DFI_FAIL=0;
DFI_ERROR=0;
DFII_SUCCESS=0;
DFII_FAIL=0;
DFII_ERROR=0;
TDFII_SUCCESS=0;
TDFII_FAIL=0;
TDFII_ERROR=0;

TOTAL_TIME=0;
TOTAL_TIMEOUT=0;
TOTAL_VERIFICATIONS=0;

echo "*** DSVerifier Benchmarks Results Extractor v1.0 - $FOLDER ***";

for file in $FILES; do

	TOTAL_VERIFICATIONS=$((TOTAL_VERIFICATIONS + 1));
	DS_NUMBER=$(echo $file | cut -d "-" -f2);
	IMPL_NUMBER=$(echo $file | cut -d "-" -f3);
	TEST_NUMBER="$DS_NUMBER-$IMPL_NUMBER";
  
	if [ $CURRENT != $TEST_NUMBER ]; then
		echo $LINE;
		LINE="$TEST_NUMBER ";
		CURRENT=$TEST_NUMBER; 
	fi
   
	FORM=$(echo $file | cut -d "-" -f4 | cut -d "." -f1);

	ERROR=$(cat $file | grep "ERROR\|bad_alloc" | wc -l)  
	FAILED=$(cat $file | grep -i "VERIFICATION FAILED" | wc -l)   
	TIMEOUT=$(cat $file | grep -i "Timed Out" | wc -l)
	MINUTES=$(tac $file | head -n5 | grep real | cut -f2 | cut -d "m" -f1)
	SECONDS=$(tac $file | head -n5 | grep real | cut -f2 | cut -d "m" -f2 | cut -d "." -f1 )
	TIME=$((MINUTES * 60 + SECONDS))
	
	if [ $TIME -eq 0 ]; then
		TIME="<1";
	fi

	if [ $ERROR -ge 1 ] && [ $FAILED -eq 0 ] && [ $TIMEOUT -eq 0 ]; then
		RESULT="E";
	elif [ $ERROR -ge 1 ] && [ $FAILED -eq 1 ] && [ $TIMEOUT -eq 0 ]; then
		RESULT="E";
	elif [ $FAILED -eq 0 ] && [ $TIMEOUT -eq 0 ]; then
		RESULT="S";
	elif [ $FAILED -eq 1 ] && [ $TIMEOUT -eq 0 ]; then
		RESULT="F";
	else
		RESULT="T";
		TOTAL_TIMEOUT=$((TOTAL_TIMEOUT + 1));
	fi

	LINE="$LINE $RESULT $TIME"
	
	TOTAL_TIME=$((TOTAL_TIME + TIME));
	if [ $RESULT == "S" ]; then
		if [ "$FORM" == "DFI" ]; then
			DFI_SUCCESS=$((DFI_SUCCESS + 1));
		elif [ "$FORM" == "DFII" ]; then
			DFII_SUCCESS=$((DFII_SUCCESS + 1));
		elif [ "$FORM" == "TDFII" ]; then
			TDFII_SUCCESS=$((TDFII_SUCCESS + 1));
		fi
	fi
	if [ $RESULT == "F" ]; then
		if [ "$FORM" == "DFI" ]; then
			DFI_FAIL=$((DFI_FAIL + 1));
		elif [ "$FORM" == "DFII" ]; then
			DFII_FAIL=$((DFII_FAIL + 1));
		elif [ "$FORM" == "TDFII" ]; then
			TDFII_FAIL=$((TDFII_FAIL + 1));
		fi
	fi
	if [ $RESULT == "E" ]; then
		if [ "$FORM" == "DFI" ]; then
			DFI_ERROR=$((DFI_ERROR + 1));
		elif [ "$FORM" == "DFII" ]; then
			DFII_ERROR=$((DFII_ERROR + 1));
		elif [ "$FORM" == "TDFII" ]; then
			TDFII_ERROR=$((TDFII_ERROR + 1));
		fi
	fi

done

echo "$LINE";

# show report
echo "";
echo "*** RESULTS *** ";
echo "Total of verifications: $TOTAL_VERIFICATIONS";
echo "";
echo "* DIRECT FORM I (DFI) *";
echo "Total of success: $DFI_SUCCESS";
echo "Total of fails: $DFI_FAIL";
echo "Total of error: $DFI_ERROR";
echo "";
echo "* DIRECT FORM II (DFII) *";
echo "Total of success: $DFII_SUCCESS";
echo "Total of fails: $DFII_FAIL";
echo "Total of error: $DFII_ERROR";
echo "";
echo "* TRANSPOSED DIRECT FORM II (TDFII) *";
echo "Total of success: $TDFII_SUCCESS";
echo "Total of fails: $TDFII_FAIL";
echo "Total of error: $TDFII_ERROR";
echo "";
echo "Total time (s): $TOTAL_TIME";
echo "Total of timeouts: $TOTAL_TIMEOUT";

cd $PREVIOUS_FOLDER;
