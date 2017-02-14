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
verifyStateSpaceObservability(dcmotor_ss_disc1, inputs, 12,4,1,-1,'');
disp('running dcmotor_ss_disc2');
verifyStateSpaceObservability(dcmotor_ss_disc2, inputs, 2,14,1,-1,'');
disp('running dcmotor_ss_disc3');
verifyStateSpaceObservability(dcmotor_ss_disc3, inputs, 10,6,1,-1,'');
disp('running dcmotor_ss_disc4');
verifyStateSpaceObservability(dcmotor_ss_disc4, inputs, 8,8,1,-1,'');
disp('running dcmotor_ss_disc5');
verifyStateSpaceObservability(dcmotor_ss_disc5, inputs, 6,10,1,-1,'');
disp('running dcmotor_ss_disc6');
verifyStateSpaceObservability(dcmotor_ss_disc6, inputs, 7,9,1,-1,'');
disp('running dcmotor_ss_disc7');
verifyStateSpaceObservability(dcmotor_ss_disc7, inputs, 9,7,1,-1,'');
disp('running dcmotor_ss_disc8');
verifyStateSpaceObservability(dcmotor_ss_disc8, inputs, 11,5,1,-1,'');

disp('running pendulum_ss_disc1');
verifyStateSpaceObservability(pendulum_ss_disc1, inputs, 12,4,1,-1,'');
disp('running pendulum_ss_disc2');
verifyStateSpaceObservability(pendulum_ss_disc2, inputs, 2,14,1,-1,'');
disp('running pendulum_ss_disc3');
verifyStateSpaceObservability(pendulum_ss_disc3, inputs, 10,6,1,-1,'');
disp('running pendulum_ss_disc4');
verifyStateSpaceObservability(pendulum_ss_disc4, inputs, 8,8,1,-1,'');
disp('running pendulum_ss_disc5');
verifyStateSpaceObservability(pendulum_ss_disc5, inputs, 6,10,1,-1,'');
disp('running pendulum_ss_disc6');
verifyStateSpaceObservability(pendulum_ss_disc6, inputs, 7,9,1,-1,'');
disp('running pendulum_ss_disc7');
verifyStateSpaceObservability(pendulum_ss_disc7, inputs, 9,7,1,-1,'');
disp('running pendulum_ss_disc8');
verifyStateSpaceObservability(pendulum_ss_disc8, inputs, 11,5,1,-1,'');

disp('running invpendulum_cartpos_ss_disc1');
verifyStateSpaceObservability(invpendulum_cartpos_ss_disc1, inputs, 12,4,1,-1,'');
disp('running invpendulum_cartpos_ss_disc2');
verifyStateSpaceObservability(invpendulum_cartpos_ss_disc2, inputs, 2,14,1,-1,'');
disp('running invpendulum_cartpos_ss_disc3');
verifyStateSpaceObservability(invpendulum_cartpos_ss_disc3, inputs, 10,6,1,-1,'');
disp('running invpendulum_cartpos_ss_disc4');
verifyStateSpaceObservability(invpendulum_cartpos_ss_disc4, inputs, 8,8,1,-1,'');
disp('running invpendulum_cartpos_ss_disc5');
verifyStateSpaceObservability(invpendulum_cartpos_ss_disc5, inputs, 6,10,1,-1,'');
disp('running invpendulum_cartpos_ss_disc6');
verifyStateSpaceObservability(invpendulum_cartpos_ss_disc6, inputs, 7,9,1,-1,'');
disp('running invpendulum_cartpos_ss_disc7');
verifyStateSpaceObservability(invpendulum_cartpos_ss_disc7, inputs, 9,7,1,-1,'');
disp('running invpendulum_cartpos_ss_disc8');
verifyStateSpaceObservability(invpendulum_cartpos_ss_disc8, inputs, 11,5,1,-1,'');

disp('running magsuspension_ss_disc1');
verifyStateSpaceObservability(magsuspension_ss_disc1, inputs, 12,4,1,-1,'');
disp('running magsuspension_ss_disc2');
verifyStateSpaceObservability(magsuspension_ss_disc2, inputs, 2,14,1,-1,'');
disp('running magsuspension_ss_disc3');
verifyStateSpaceObservability(magsuspension_ss_disc3, inputs, 10,6,1,-1,'');
disp('running magsuspension_ss_disc4');
verifyStateSpaceObservability(magsuspension_ss_disc4, inputs, 8,8,1,-1,'');
disp('running magsuspension_ss_disc5');
verifyStateSpaceObservability(magsuspension_ss_disc5, inputs, 6,10,1,-1,'');
disp('running magsuspension_ss_disc6');
verifyStateSpaceObservability(magsuspension_ss_disc6, inputs, 7,9,1,-1,'');
disp('running magsuspension_ss_disc7');
verifyStateSpaceObservability(magsuspension_ss_disc7, inputs, 9,7,1,-1,'');
disp('running magsuspension_ss_disc8');
verifyStateSpaceObservability(magsuspension_ss_disc8, inputs, 11,5,1,-1,'');

disp('running cruise_ss_disc1');
verifyStateSpaceObservability(cruise_ss_disc1, inputs, 12,4,1,-1,'');
disp('running cruise_ss_disc2');
verifyStateSpaceObservability(cruise_ss_disc2, inputs, 2,14,1,-1,'');
disp('running cruise_ss_disc3');
verifyStateSpaceObservability(cruise_ss_disc3, inputs, 10,6,1,-1,'');
disp('running cruise_ss_disc4');
verifyStateSpaceObservability(cruise_ss_disc4, inputs, 8,8,1,-1,'');
disp('running cruise_ss_disc5');
verifyStateSpaceObservability(cruise_ss_disc5, inputs, 6,10,1,-1,'');
disp('running cruise_ss_disc6');
verifyStateSpaceObservability(cruise_ss_disc6, inputs, 7,9,1,-1,'');
disp('running cruise_ss_disc7');
verifyStateSpaceObservability(cruise_ss_disc7, inputs, 9,7,1,-1,'');

disp('running tapedriver_ss_disc1');
verifyStateSpaceObservability(tapedriver_ss_disc1, inputs, 12,4,1,-1,'');
disp('running tapedriver_ss_disc2');
verifyStateSpaceObservability(tapedriver_ss_disc2, inputs, 2,14,1,-1,'');
disp('running tapedriver_ss_disc3');
verifyStateSpaceObservability(tapedriver_ss_disc3, inputs, 10,6,1,-1,'');
disp('running tapedriver_ss_disc4');
verifyStateSpaceObservability(tapedriver_ss_disc4, inputs, 8,8,1,-1,'');
disp('running tapedriver_ss_disc5');
verifyStateSpaceObservability(tapedriver_ss_disc5, inputs, 6,10,1,-1,'');
disp('running tapedriver_ss_disc6');
verifyStateSpaceObservability(tapedriver_ss_disc6, inputs, 7,9,1,-1,'');
disp('running tapedriver_ss_disc7');
verifyStateSpaceObservability(tapedriver_ss_disc7, inputs, 9,7,1,-1,'');
disp('running tapedriver_ss_disc8');
verifyStateSpaceObservability(tapedriver_ss_disc8, inputs, 11,5,1,-1,'');

disp('running helicopter_ss_disc1');
verifyStateSpaceObservability(helicopter_ss_disc1, inputs, 12,4,1,-1,'');
disp('running helicopter_ss_disc2');
verifyStateSpaceObservability(helicopter_ss_disc2, inputs, 2,14,1,-1,'');
disp('running helicopter_ss_disc3');
verifyStateSpaceObservability(helicopter_ss_disc3, inputs, 10,6,1,-1,'');
disp('running helicopter_ss_disc4');
verifyStateSpaceObservability(helicopter_ss_disc4, inputs, 8,8,1,-1,'');
disp('running helicopter_ss_disc5');
verifyStateSpaceObservability(helicopter_ss_disc5, inputs, 6,10,1,-1,'');
disp('running helicopter_ss_disc6');
verifyStateSpaceObservability(helicopter_ss_disc6, inputs, 7,9,1,-1,'');
disp('running helicopter_ss_disc7');
verifyStateSpaceObservability(helicopter_ss_disc7, inputs, 9,7,1,-1,'');
disp('running helicopter_ss_disc8');
verifyStateSpaceObservability(helicopter_ss_disc8, inputs, 11,5,1,-1,'');

disp('running uscgtampa_ss_disc1');
verifyStateSpaceObservability(uscgtampa_ss_disc1, inputs, 12,4,1,-1,'');
disp('running uscgtampa_ss_disc2');
verifyStateSpaceObservability(uscgtampa_ss_disc2, inputs, 2,14,1,-1,'');
disp('running uscgtampa_ss_disc3');
verifyStateSpaceObservability(uscgtampa_ss_disc3, inputs, 10,6,1,-1,'');
disp('running uscgtampa_ss_disc4');
verifyStateSpaceObservability(uscgtampa_ss_disc4, inputs, 8,8,1,-1,'');
disp('running uscgtampa_ss_disc5');
verifyStateSpaceObservability(uscgtampa_ss_disc5, inputs, 6,10,1,-1,'');
disp('running uscgtampa_ss_disc6');
verifyStateSpaceObservability(uscgtampa_ss_disc6, inputs, 7,9,1,-1,'');
disp('running uscgtampa_ss_disc7');
verifyStateSpaceObservability(uscgtampa_ss_disc7, inputs, 9,7,1,-1,'');
disp('running uscgtampa_ss_disc8');
verifyStateSpaceObservability(uscgtampa_ss_disc8, inputs, 11,5,1,-1,'');

disp('running magneticpointer_ss_disc1');
verifyStateSpaceObservability(magneticpointer_ss_disc1, inputs, 12,4,1,-1,'');
disp('running magneticpointer_ss_disc2');
verifyStateSpaceObservability(magneticpointer_ss_disc2, inputs, 2,14,1,-1,'');
disp('running magneticpointer_ss_disc3');
verifyStateSpaceObservability(magneticpointer_ss_disc3, inputs, 10,6,1,-1,'');
disp('running magneticpointer_ss_disc4');
verifyStateSpaceObservability(magneticpointer_ss_disc4, inputs, 8,8,1,-1,'');
disp('running magneticpointer_ss_disc5');
verifyStateSpaceObservability(magneticpointer_ss_disc5, inputs, 6,10,1,-1,'');
disp('running magneticpointer_ss_disc6');
verifyStateSpaceObservability(magneticpointer_ss_disc6, inputs, 7,9,1,-1,'');
disp('running magneticpointer_ss_disc7');
verifyStateSpaceObservability(magneticpointer_ss_disc7, inputs, 9,7,1,-1,'');
disp('running magneticpointer_ss_disc8');
verifyStateSpaceObservability(magneticpointer_ss_disc8, inputs, 11,5,1,-1,'');
