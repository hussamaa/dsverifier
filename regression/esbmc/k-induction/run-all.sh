#!/bin/bash

total_time=0

MODULES="digital-system overflow-delta-I overflow-delta-II overflow-direct-I overflow-direct-II limit-cycle-delta-I limit-cycle-delta-II limit-cycle-direct-I limit-cycle-direct-II"

echo ""
echo "Script for DSVerifier started at:" $(date +"%T")
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
  echo "Time elapsed for" $module ":" $(( $END - $START )) "s"
  time=$(( $END - $START ))
  total_time=`echo $total_time + $time | bc -l`
  echo "Total time elapsed: " $total_time "s"
done
echo "============================== "

echo ""
echo "Script DSVerifier ended at:" $(date +"%T")
echo ""


