clc;
close all;
clear all;

load('matlab');

%Test DFI Realizations
check_absence_limit_cycle(system_dfi);
%Test DFII Realizations
check_absence_limit_cycle(system_dfii);
%Test TDFII Realizations
check_absence_limit_cycle(system_tdfii);