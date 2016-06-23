#!/bin/bash
#
# DSVerifier - Script to Compare Results between MATLAB and DSverifier
#
#               Universidade Federal do Amazonas - UFAM
# Author:       Lennon Chaves <lennon.correach@gmail.com>
#
# ------------------------------------------------------
#
# Script to compare results between MATLAB and DSverifier
# 
# Usage Example:
# $ sh script dsverifier.out matlab.out
#
# ------------------------------------------------------

file1=$1;
file2=$2;

if test $# -ne 2; then
   echo "usage: $0 file1.out file2.out" >&2
   exit 1
fi

echo "";
echo "*** RESULTS *** ";
echo "";

INDICE=0;
paste $file1 $file2 | while IFS="$(printf '\t')" read -r f1 f2
do
INDICE=$((INDICE+1));

if [ "$f1" = "$f2" ]; then
   echo "Teste: $INDICE $(echo -e "\033[0;32mSuccess\033[0m" | cut -d " " -f2)";  
else
   echo "Teste: $INDICE $(echo -e "\\033[0;31mFail\033[0m" | cut -d " " -f2)";       
fi
done
