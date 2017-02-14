makebenchmarks

clear all
clc

load('benchmark_ss.mat')

%DC Motor - 8 benchmarks - dcmotor_ss_disc
%Pendulum - 8 benchmarks - pendulum_ss_disc
%Inverted Cart Pendulum - 8 benchmarks - invpendulum_cartpos_ss_disc 
%Simple Magnetic Suspension System - 8 benchmarks - magsuspension_ss_disc
%Car Cruise Control - 7 benchmarks - cruise_ss_disc
%Computer Tape Driver - 8 benchmarks - tapedriver_ss_disc
%Helicopter Longitudinal Motion - 8 benchmarks - helicopter_ss_disc
%USCG cutter Tampa Heading Angle - 8 benchmarks - uscgtampa_ss_disc
%Magnetic Pointer - 8 benchmarks -magneticpointer_ss_disc

%Inputs

inputs = [1.0];

disp('running dcmotor_ss_disc1');
verifyStateSpaceQuantizationError(dcmotor_ss_disc1, inputs, 12,4,1,-1,0.18, 10, '');
disp('running dcmotor_ss_disc2');
verifyStateSpaceQuantizationError(dcmotor_ss_disc2, inputs, 2,14,1,-1,0.18, 10, '');
disp('running dcmotor_ss_disc3');
verifyStateSpaceQuantizationError(dcmotor_ss_disc3, inputs, 10,6,1,-1,0.18, 10, '');
disp('running dcmotor_ss_disc4');
verifyStateSpaceQuantizationError(dcmotor_ss_disc4, inputs, 8,8,1,-1,0.18, 10, '');
disp('running dcmotor_ss_disc5');
verifyStateSpaceQuantizationError(dcmotor_ss_disc5, inputs, 6,10,1,-1,0.18, 10, '');
disp('running dcmotor_ss_disc6');
verifyStateSpaceQuantizationError(dcmotor_ss_disc6, inputs, 7,9,1,-1,0.18, 10, '');
disp('running dcmotor_ss_disc7');
verifyStateSpaceQuantizationError(dcmotor_ss_disc7, inputs, 9,7,1,-1,0.18, 10, '');
disp('running dcmotor_ss_disc8');
verifyStateSpaceQuantizationError(dcmotor_ss_disc8, inputs, 11,5,1,-1,0.18, 10, '');

disp('running pendulum_ss_disc1');
verifyStateSpaceQuantizationError(pendulum_ss_disc1, inputs, 12,4,1,-1,0.18, 10, '');
disp('running pendulum_ss_disc2');
verifyStateSpaceQuantizationError(pendulum_ss_disc2, inputs, 2,14,1,-1,0.18, 10, '');
disp('running pendulum_ss_disc3');
verifyStateSpaceQuantizationError(pendulum_ss_disc3, inputs, 10,6,1,-1,0.18, 10, '');
disp('running pendulum_ss_disc4');
verifyStateSpaceQuantizationError(pendulum_ss_disc4, inputs, 8,8,1,-1,0.18, 10, '');
disp('running pendulum_ss_disc5');
verifyStateSpaceQuantizationError(pendulum_ss_disc5, inputs, 6,10,1,-1,0.18, 10, '');
disp('running pendulum_ss_disc6');
verifyStateSpaceQuantizationError(pendulum_ss_disc6, inputs, 7,9,1,-1,0.18, 10, '');
disp('running pendulum_ss_disc7');
verifyStateSpaceQuantizationError(pendulum_ss_disc7, inputs, 9,7,1,-1,0.18, 10, '');
disp('running pendulum_ss_disc8');
verifyStateSpaceQuantizationError(pendulum_ss_disc8, inputs, 11,5,1,-1,0.18, 10, '');

disp('running invpendulum_cartpos_ss_disc1');
verifyStateSpaceQuantizationError(invpendulum_cartpos_ss_disc1, inputs, 12,4,1,-1,0.18, 10, '');
disp('running invpendulum_cartpos_ss_disc2');
verifyStateSpaceQuantizationError(invpendulum_cartpos_ss_disc2, inputs, 2,14,1,-1,0.18, 10, '');
disp('running invpendulum_cartpos_ss_disc3');
verifyStateSpaceQuantizationError(invpendulum_cartpos_ss_disc3, inputs, 10,6,1,-1,0.18, 10, '');
disp('running invpendulum_cartpos_ss_disc4');
verifyStateSpaceQuantizationError(invpendulum_cartpos_ss_disc4, inputs, 8,8,1,-1,0.18, 10, '');
disp('running invpendulum_cartpos_ss_disc5');
verifyStateSpaceQuantizationError(invpendulum_cartpos_ss_disc5, inputs, 6,10,1,-1,0.18, 10, '');
disp('running invpendulum_cartpos_ss_disc6');
verifyStateSpaceQuantizationError(invpendulum_cartpos_ss_disc6, inputs, 7,9,1,-1,0.18, 10, '');
disp('running invpendulum_cartpos_ss_disc7');
verifyStateSpaceQuantizationError(invpendulum_cartpos_ss_disc7, inputs, 9,7,1,-1,0.18, 10, '');
disp('running invpendulum_cartpos_ss_disc8');
verifyStateSpaceQuantizationError(invpendulum_cartpos_ss_disc8, inputs, 11,5,1,-1,0.18, 10, '');

disp('running magsuspension_ss_disc1');
verifyStateSpaceQuantizationError(magsuspension_ss_disc1, inputs, 12,4,1,-1,0.18, 10, '');
disp('running magsuspension_ss_disc2');
verifyStateSpaceQuantizationError(magsuspension_ss_disc2, inputs, 2,14,1,-1,0.18, 10, '');
disp('running magsuspension_ss_disc3');
verifyStateSpaceQuantizationError(magsuspension_ss_disc3, inputs, 10,6,1,-1,0.18, 10, '');
disp('running magsuspension_ss_disc4');
verifyStateSpaceQuantizationError(magsuspension_ss_disc4, inputs, 8,8,1,-1,0.18, 10, '');
disp('running magsuspension_ss_disc5');
verifyStateSpaceQuantizationError(magsuspension_ss_disc5, inputs, 6,10,1,-1,0.18, 10, '');
disp('running magsuspension_ss_disc6');
verifyStateSpaceQuantizationError(magsuspension_ss_disc6, inputs, 7,9,1,-1,0.18, 10, '');
disp('running magsuspension_ss_disc7');
verifyStateSpaceQuantizationError(magsuspension_ss_disc7, inputs, 9,7,1,-1,0.18, 10, '');
disp('running magsuspension_ss_disc8');
verifyStateSpaceQuantizationError(magsuspension_ss_disc8, inputs, 11,5,1,-1,0.18, 10, '');

disp('running cruise_ss_disc1');
verifyStateSpaceQuantizationError(cruise_ss_disc1, inputs, 12,4,1,-1,0.18, 10, '');
disp('running cruise_ss_disc2');
verifyStateSpaceQuantizationError(cruise_ss_disc2, inputs, 2,14,1,-1,0.18, 10, '');
disp('running cruise_ss_disc3');
verifyStateSpaceQuantizationError(cruise_ss_disc3, inputs, 10,6,1,-1,0.18, 10, '');
disp('running cruise_ss_disc4');
verifyStateSpaceQuantizationError(cruise_ss_disc4, inputs, 8,8,1,-1,0.18, 10, '');
disp('running cruise_ss_disc5');
verifyStateSpaceQuantizationError(cruise_ss_disc5, inputs, 6,10,1,-1,0.18, 10, '');
disp('running cruise_ss_disc6');
verifyStateSpaceQuantizationError(cruise_ss_disc6, inputs, 7,9,1,-1,0.18, 10, '');
disp('running cruise_ss_disc7');
verifyStateSpaceQuantizationError(cruise_ss_disc7, inputs, 9,7,1,-1,0.18, 10, '');

disp('running tapedriver_ss_disc1');
verifyStateSpaceQuantizationError(tapedriver_ss_disc1, inputs, 12,4,1,-1,0.18, 10, '');
disp('running tapedriver_ss_disc2');
verifyStateSpaceQuantizationError(tapedriver_ss_disc2, inputs, 2,14,1,-1,0.18, 10, '');
disp('running tapedriver_ss_disc3');
verifyStateSpaceQuantizationError(tapedriver_ss_disc3, inputs, 10,6,1,-1,0.18, 10, '');
disp('running tapedriver_ss_disc4');
verifyStateSpaceQuantizationError(tapedriver_ss_disc4, inputs, 8,8,1,-1,0.18, 10, '');
disp('running tapedriver_ss_disc5');
verifyStateSpaceQuantizationError(tapedriver_ss_disc5, inputs, 6,10,1,-1,0.18, 10, '');
disp('running tapedriver_ss_disc6');
verifyStateSpaceQuantizationError(tapedriver_ss_disc6, inputs, 7,9,1,-1,0.18, 10, '');
disp('running tapedriver_ss_disc7');
verifyStateSpaceQuantizationError(tapedriver_ss_disc7, inputs, 9,7,1,-1,0.18, 10, '');
disp('running tapedriver_ss_disc8');
verifyStateSpaceQuantizationError(tapedriver_ss_disc8, inputs, 11,5,1,-1,0.18, 10, '');

disp('running helicopter_ss_disc1');
verifyStateSpaceQuantizationError(helicopter_ss_disc1, inputs, 12,4,1,-1,0.18, 10, '');
disp('running helicopter_ss_disc2');
verifyStateSpaceQuantizationError(helicopter_ss_disc2, inputs, 2,14,1,-1,0.18, 10, '');
disp('running helicopter_ss_disc3');
verifyStateSpaceQuantizationError(helicopter_ss_disc3, inputs, 10,6,1,-1,0.18, 10, '');
disp('running helicopter_ss_disc4');
verifyStateSpaceQuantizationError(helicopter_ss_disc4, inputs, 8,8,1,-1,0.18, 10, '');
disp('running helicopter_ss_disc5');
verifyStateSpaceQuantizationError(helicopter_ss_disc5, inputs, 6,10,1,-1,0.18, 10, '');
disp('running helicopter_ss_disc6');
verifyStateSpaceQuantizationError(helicopter_ss_disc6, inputs, 7,9,1,-1,0.18, 10, '');
disp('running helicopter_ss_disc7');
verifyStateSpaceQuantizationError(helicopter_ss_disc7, inputs, 9,7,1,-1,0.18, 10, '');
disp('running helicopter_ss_disc8');
verifyStateSpaceQuantizationError(helicopter_ss_disc8, inputs, 11,5,1,-1,0.18, 10, '');

disp('running uscgtampa_ss_disc1');
verifyStateSpaceQuantizationError(uscgtampa_ss_disc1, inputs, 12,4,1,-1,0.18, 10, '');
disp('running uscgtampa_ss_disc2');
verifyStateSpaceQuantizationError(uscgtampa_ss_disc2, inputs, 2,14,1,-1,0.18, 10, '');
disp('running uscgtampa_ss_disc3');
verifyStateSpaceQuantizationError(uscgtampa_ss_disc3, inputs, 10,6,1,-1,0.18, 10, '');
disp('running uscgtampa_ss_disc4');
verifyStateSpaceQuantizationError(uscgtampa_ss_disc4, inputs, 8,8,1,-1,0.18, 10, '');
disp('running uscgtampa_ss_disc5');
verifyStateSpaceQuantizationError(uscgtampa_ss_disc5, inputs, 6,10,1,-1,0.18, 10, '');
disp('running uscgtampa_ss_disc6');
verifyStateSpaceQuantizationError(uscgtampa_ss_disc6, inputs, 7,9,1,-1,0.18, 10, '');
disp('running uscgtampa_ss_disc7');
verifyStateSpaceQuantizationError(uscgtampa_ss_disc7, inputs, 9,7,1,-1,0.18, 10, '');
disp('running uscgtampa_ss_disc8');
verifyStateSpaceQuantizationError(uscgtampa_ss_disc8, inputs, 11,5,1,-1,0.18, 10, '');

disp('running magneticpointer_ss_disc1');
verifyStateSpaceQuantizationError(magneticpointer_ss_disc1, inputs, 12,4,1,-1,0.18, 10, '');
disp('running magneticpointer_ss_disc2');
verifyStateSpaceQuantizationError(magneticpointer_ss_disc2, inputs, 2,14,1,-1,0.18, 10, '');
disp('running magneticpointer_ss_disc3');
verifyStateSpaceQuantizationError(magneticpointer_ss_disc3, inputs, 10,6,1,-1,0.18, 10, '');
disp('running magneticpointer_ss_disc4');
verifyStateSpaceQuantizationError(magneticpointer_ss_disc4, inputs, 8,8,1,-1,0.18, 10, '');
disp('running magneticpointer_ss_disc5');
verifyStateSpaceQuantizationError(magneticpointer_ss_disc5, inputs, 6,10,1,-1,0.18, 10, '');
disp('running magneticpointer_ss_disc6');
verifyStateSpaceQuantizationError(magneticpointer_ss_disc6, inputs, 7,9,1,-1,0.18, 10, '');
disp('running magneticpointer_ss_disc7');
verifyStateSpaceQuantizationError(magneticpointer_ss_disc7, inputs, 9,7,1,-1,0.18, 10, '');
disp('running magneticpointer_ss_disc8');
verifyStateSpaceQuantizationError(magneticpointer_ss_disc8, inputs, 11,5,1,-1,0.18, 10, '');
