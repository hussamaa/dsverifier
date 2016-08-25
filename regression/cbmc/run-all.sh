#!/bin/bash

MODULES="closed-loop digital-system white-box"

echo ""
echo "Script DSVerifier Started:" $(date +"%T")
echo ""

for module in $MODULES; do
  echo "============================== "
  echo -n "Running" $module...
  cd $module
  make clean > /dev/null 
  START=$(date +"%s")
  make 
  END=$(date +"%s")
  echo "Done!"
  make clean > /dev/null 
  cd ..
  echo "Time elapsed: " $(( $END - $START )) "s"
  echo "Time elapsed: " $(( $END - $START )) "s"
done
echo "============================== "

echo ""
echo "Script DSVerifier Ended:" $(date +"%T")
echo ""


