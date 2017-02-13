%%%%%%%%%%
% 
% This file builds the test suite for DS tools
%
% Written by:
%   Iury Bessa
%   Manaus, 2016
%%%%%%%%%%
%%
clc; clear all;
display('Creating test suite for DS Tools...')
dcmotor
display('DC Motor - 8 benchmarks')
hscc
display('HSCC 2017 - 6 benchmarks')
pendulum
display('Pendulum - 8 benchmarks')
invertedpendulum
display('Inverted Cart Pendulum - 16 benchmarks')
suspension
display('1/4 Car Suspension System - 7 benchmarks')
magneticsuspension
display('Simple Magnetic Suspension System - 8 benchmarks')
cruise
display('Car Cruise Control - 7 benchmarks')
tapedriver
display('Computer Tape Driver - 8 benchmarks')
helicopter
display('Helicopter Longitudinal Motion - 8 benchmarks')
uscgtampa
display('USCG cutter Tampa Heading Angle - 8 benchmarks')
magneticpointer
display('Magnetic Pointer - 8 benchmarks')
display('Done')
display('Total of benchmarks: 92')
display('The .mat file benchmark_tf.mat contains the transfer function models.')
display('The .mat file benchmark_ss.mat contains the state space models.')