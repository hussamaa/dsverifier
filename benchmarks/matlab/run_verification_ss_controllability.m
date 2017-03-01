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
verifyStateSpaceControllability(dcmotor_ss_disc1, inputs, 12,4,1,-1,'');
disp('running dcmotor_ss_disc2');
verifyStateSpaceControllability(dcmotor_ss_disc2, inputs, 2,14,1,-1,'');
disp('running dcmotor_ss_disc3');
verifyStateSpaceControllability(dcmotor_ss_disc3, inputs, 10,6,1,-1,'');
disp('running dcmotor_ss_disc4');
verifyStateSpaceControllability(dcmotor_ss_disc4, inputs, 8,8,1,-1,'');
disp('running dcmotor_ss_disc5');
verifyStateSpaceControllability(dcmotor_ss_disc5, inputs, 6,10,1,-1,'');
disp('running dcmotor_ss_disc6');
verifyStateSpaceControllability(dcmotor_ss_disc6, inputs, 7,9,1,-1,'');
disp('running dcmotor_ss_disc7');
verifyStateSpaceControllability(dcmotor_ss_disc7, inputs, 9,7,1,-1,'');
disp('running dcmotor_ss_disc8');
verifyStateSpaceControllability(dcmotor_ss_disc8, inputs, 11,5,1,-1,'');

disp('running pendulum_ss_disc1');
verifyStateSpaceControllability(pendulum_ss_disc1, inputs, 12,4,1,-1,'');
disp('running pendulum_ss_disc2');
verifyStateSpaceControllability(pendulum_ss_disc2, inputs, 2,14,1,-1,'');
disp('running pendulum_ss_disc3');
verifyStateSpaceControllability(pendulum_ss_disc3, inputs, 10,6,1,-1,'');
disp('running pendulum_ss_disc4');
verifyStateSpaceControllability(pendulum_ss_disc4, inputs, 8,8,1,-1,'');
disp('running pendulum_ss_disc5');
verifyStateSpaceControllability(pendulum_ss_disc5, inputs, 6,10,1,-1,'');
disp('running pendulum_ss_disc6');
verifyStateSpaceControllability(pendulum_ss_disc6, inputs, 7,9,1,-1,'');
disp('running pendulum_ss_disc7');
verifyStateSpaceControllability(pendulum_ss_disc7, inputs, 9,7,1,-1,'');
disp('running pendulum_ss_disc8');
verifyStateSpaceControllability(pendulum_ss_disc8, inputs, 11,5,1,-1,'');

disp('running invpendulum_cartpos_ss_disc1');
verifyStateSpaceControllability(invpendulum_cartpos_ss_disc1, inputs, 12,4,1,-1,'');
disp('running invpendulum_cartpos_ss_disc2');
verifyStateSpaceControllability(invpendulum_cartpos_ss_disc2, inputs, 2,14,1,-1,'');
disp('running invpendulum_cartpos_ss_disc3');
verifyStateSpaceControllability(invpendulum_cartpos_ss_disc3, inputs, 10,6,1,-1,'');
disp('running invpendulum_cartpos_ss_disc4');
verifyStateSpaceControllability(invpendulum_cartpos_ss_disc4, inputs, 8,8,1,-1,'');
disp('running invpendulum_cartpos_ss_disc5');
verifyStateSpaceControllability(invpendulum_cartpos_ss_disc5, inputs, 6,10,1,-1,'');
disp('running invpendulum_cartpos_ss_disc6');
verifyStateSpaceControllability(invpendulum_cartpos_ss_disc6, inputs, 7,9,1,-1,'');
disp('running invpendulum_cartpos_ss_disc7');
verifyStateSpaceControllability(invpendulum_cartpos_ss_disc7, inputs, 9,7,1,-1,'');
disp('running invpendulum_cartpos_ss_disc8');
verifyStateSpaceControllability(invpendulum_cartpos_ss_disc8, inputs, 11,5,1,-1,'');

disp('running magsuspension_ss_disc1');
verifyStateSpaceControllability(magsuspension_ss_disc1, inputs, 12,4,1,-1,'');
disp('running magsuspension_ss_disc2');
verifyStateSpaceControllability(magsuspension_ss_disc2, inputs, 2,14,1,-1,'');
disp('running magsuspension_ss_disc3');
verifyStateSpaceControllability(magsuspension_ss_disc3, inputs, 10,6,1,-1,'');
disp('running magsuspension_ss_disc4');
verifyStateSpaceControllability(magsuspension_ss_disc4, inputs, 8,8,1,-1,'');
disp('running magsuspension_ss_disc5');
verifyStateSpaceControllability(magsuspension_ss_disc5, inputs, 6,10,1,-1,'');
disp('running magsuspension_ss_disc6');
verifyStateSpaceControllability(magsuspension_ss_disc6, inputs, 7,9,1,-1,'');
disp('running magsuspension_ss_disc7');
verifyStateSpaceControllability(magsuspension_ss_disc7, inputs, 9,7,1,-1,'');
disp('running magsuspension_ss_disc8');
verifyStateSpaceControllability(magsuspension_ss_disc8, inputs, 11,5,1,-1,'');

disp('running cruise_ss_disc1');
verifyStateSpaceControllability(cruise_ss_disc1, inputs, 12,4,1,-1,'');
disp('running cruise_ss_disc2');
verifyStateSpaceControllability(cruise_ss_disc2, inputs, 2,14,1,-1,'');
disp('running cruise_ss_disc3');
verifyStateSpaceControllability(cruise_ss_disc3, inputs, 10,6,1,-1,'');
disp('running cruise_ss_disc4');
verifyStateSpaceControllability(cruise_ss_disc4, inputs, 8,8,1,-1,'');
disp('running cruise_ss_disc5');
verifyStateSpaceControllability(cruise_ss_disc5, inputs, 6,10,1,-1,'');
disp('running cruise_ss_disc6');
verifyStateSpaceControllability(cruise_ss_disc6, inputs, 7,9,1,-1,'');
disp('running cruise_ss_disc7');
verifyStateSpaceControllability(cruise_ss_disc7, inputs, 9,7,1,-1,'');

disp('running tapedriver_ss_disc1');
verifyStateSpaceControllability(tapedriver_ss_disc1, inputs, 12,4,1,-1,'');
disp('running tapedriver_ss_disc2');
verifyStateSpaceControllability(tapedriver_ss_disc2, inputs, 2,14,1,-1,'');
disp('running tapedriver_ss_disc3');
verifyStateSpaceControllability(tapedriver_ss_disc3, inputs, 10,6,1,-1,'');
disp('running tapedriver_ss_disc4');
verifyStateSpaceControllability(tapedriver_ss_disc4, inputs, 8,8,1,-1,'');
disp('running tapedriver_ss_disc5');
verifyStateSpaceControllability(tapedriver_ss_disc5, inputs, 6,10,1,-1,'');
disp('running tapedriver_ss_disc6');
verifyStateSpaceControllability(tapedriver_ss_disc6, inputs, 7,9,1,-1,'');
disp('running tapedriver_ss_disc7');
verifyStateSpaceControllability(tapedriver_ss_disc7, inputs, 9,7,1,-1,'');
disp('running tapedriver_ss_disc8');
verifyStateSpaceControllability(tapedriver_ss_disc8, inputs, 11,5,1,-1,'');

disp('running helicopter_ss_disc1');
verifyStateSpaceControllability(helicopter_ss_disc1, inputs, 12,4,1,-1,'');
disp('running helicopter_ss_disc2');
verifyStateSpaceControllability(helicopter_ss_disc2, inputs, 2,14,1,-1,'');
disp('running helicopter_ss_disc3');
verifyStateSpaceControllability(helicopter_ss_disc3, inputs, 10,6,1,-1,'');
disp('running helicopter_ss_disc4');
verifyStateSpaceControllability(helicopter_ss_disc4, inputs, 8,8,1,-1,'');
disp('running helicopter_ss_disc5');
verifyStateSpaceControllability(helicopter_ss_disc5, inputs, 6,10,1,-1,'');
disp('running helicopter_ss_disc6');
verifyStateSpaceControllability(helicopter_ss_disc6, inputs, 7,9,1,-1,'');
disp('running helicopter_ss_disc7');
verifyStateSpaceControllability(helicopter_ss_disc7, inputs, 9,7,1,-1,'');
disp('running helicopter_ss_disc8');
verifyStateSpaceControllability(helicopter_ss_disc8, inputs, 11,5,1,-1,'');

disp('running uscgtampa_ss_disc1');
verifyStateSpaceControllability(uscgtampa_ss_disc1, inputs, 12,4,1,-1,'');
disp('running uscgtampa_ss_disc2');
verifyStateSpaceControllability(uscgtampa_ss_disc2, inputs, 2,14,1,-1,'');
disp('running uscgtampa_ss_disc3');
verifyStateSpaceControllability(uscgtampa_ss_disc3, inputs, 10,6,1,-1,'');
disp('running uscgtampa_ss_disc4');
verifyStateSpaceControllability(uscgtampa_ss_disc4, inputs, 8,8,1,-1,'');
disp('running uscgtampa_ss_disc5');
verifyStateSpaceControllability(uscgtampa_ss_disc5, inputs, 6,10,1,-1,'');
disp('running uscgtampa_ss_disc6');
verifyStateSpaceControllability(uscgtampa_ss_disc6, inputs, 7,9,1,-1,'');
disp('running uscgtampa_ss_disc7');
verifyStateSpaceControllability(uscgtampa_ss_disc7, inputs, 9,7,1,-1,'');
disp('running uscgtampa_ss_disc8');
verifyStateSpaceControllability(uscgtampa_ss_disc8, inputs, 11,5,1,-1,'');

disp('running magneticpointer_ss_disc1');
verifyStateSpaceControllability(magneticpointer_ss_disc1, inputs, 12,4,1,-1,'');
disp('running magneticpointer_ss_disc2');
verifyStateSpaceControllability(magneticpointer_ss_disc2, inputs, 2,14,1,-1,'');
disp('running magneticpointer_ss_disc3');
verifyStateSpaceControllability(magneticpointer_ss_disc3, inputs, 10,6,1,-1,'');
disp('running magneticpointer_ss_disc4');
verifyStateSpaceControllability(magneticpointer_ss_disc4, inputs, 8,8,1,-1,'');
disp('running magneticpointer_ss_disc5');
verifyStateSpaceControllability(magneticpointer_ss_disc5, inputs, 6,10,1,-1,'');
disp('running magneticpointer_ss_disc6');
verifyStateSpaceControllability(magneticpointer_ss_disc6, inputs, 7,9,1,-1,'');
disp('running magneticpointer_ss_disc7');
verifyStateSpaceControllability(magneticpointer_ss_disc7, inputs, 9,7,1,-1,'');
disp('running magneticpointer_ss_disc8');
verifyStateSpaceControllability(magneticpointer_ss_disc8, inputs, 11,5,1,-1,'');
