#!/bin/sh
# script to run all test cases
# TODO: include state-space test cases
# run chmod a+x run-all.sh
# ./run-all.sh
#
# author: Lennon Chaves
# November, 2016
# Manaus, Amazonas
#

chmod a+x cbmc/run-all.sh
chmod a+x esbmc/boolector/run-all.sh
echo "RUNNING CBMC TESTS";
cd cbmc
./run-all.sh
cd ..
echo "RUNNING ESBMC TESTS - Boolector";
cd esbmc/boolector
./run-all.sh
cd ../..
echo "RUNNING ESBMC TESTS - Z3";
cd esbmc/z3
make
