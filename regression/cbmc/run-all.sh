#!/bin/bash

MODULES="closed-loop digital-system white-box"

echo ""
echo "Script DSVerifier Started:" $(date +"%T")
echo ""

for module in $MODULES; do
  echo "============================== "
  echo -n "Running" $module...
  START=$(date +"%s")
  cd $module
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


