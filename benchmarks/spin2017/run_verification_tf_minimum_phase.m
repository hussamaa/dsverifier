makebenchmarks

clear all
clc

load('benchmark_tf.mat')

%DC Motor - 8 benchmarks - dcmotor_tf_disc
%Pendulum - 8 benchmarks - pendulum_tf_disc
%Inverted Cart Pendulum - 8 benchmarks - invpendulum_cartpos_tf_disc 
%Simple Magnetic Suspension System - 8 benchmarks - magsuspension_tf_disc
%Car Cruise Control - 7 benchmarks - cruise_tf_disc
%Computer Tape Driver - 8 benchmarks - tapedriver_tf_disc
%Helicopter Longitudinal Motion - 8 benchmarks - helicopter_tf_disc
%USCG cutter Tampa Heading Angle - 8 benchmarks - uscgtampa_tf_disc
%Magnetic Pointer - 8 benchmarks -magneticpointer_tf_disc

disp('running dcmotor_tf_disc1')
verifyMinimumPhase(dcmotor_tf_disc1,12,4,1,-1,'DFI');
disp('running dcmotor_tf_disc2')
verifyMinimumPhase(dcmotor_tf_disc2,2,14,1,-1,'DFII');
disp('running dcmotor_tf_disc3')
verifyMinimumPhase(dcmotor_tf_disc3,10,6,1,-1,'TDFII');
disp('running dcmotor_tf_disc4')
verifyMinimumPhase(dcmotor_tf_disc4,8,8,1,-1,'DFI');
disp('running dcmotor_tf_disc5')
verifyMinimumPhase(dcmotor_tf_disc5,6,10,1,-1,'DFII');
disp('running dcmotor_tf_disc6')
verifyMinimumPhase(dcmotor_tf_disc6,7,9,1,-1,'TDFII');
disp('running dcmotor_tf_disc7')
verifyMinimumPhase(dcmotor_tf_disc7,9,7,1,-1,'DFI');
disp('running dcmotor_tf_disc8')
verifyMinimumPhase(dcmotor_tf_disc8,11,5,1,-1,'DFII');

disp('running pendulum_tf_disc1')
verifyMinimumPhase(pendulum_tf_disc1,12,4,1,-1,'DFI');
disp('running pendulum_tf_disc2')
verifyMinimumPhase(pendulum_tf_disc2,2,14,1,-1,'DFII');
disp('running pendulum_tf_disc3')
verifyMinimumPhase(pendulum_tf_disc3,10,6,1,-1,'TDFII');
disp('running pendulum_tf_disc4')
verifyMinimumPhase(pendulum_tf_disc4,8,8,1,-1,'DFI');
disp('running pendulum_tf_disc5')
verifyMinimumPhase(pendulum_tf_disc5,6,10,1,-1,'DFII');
disp('running pendulum_tf_disc6')
verifyMinimumPhase(pendulum_tf_disc6,7,9,1,-1,'TDFII');
disp('running pendulum_tf_disc7')
verifyMinimumPhase(pendulum_tf_disc7,9,7,1,-1,'DFI');
disp('running pendulum_tf_disc8')
verifyMinimumPhase(pendulum_tf_disc8,11,5,1,-1,'DFII');

disp('running invpendulum_cartpos_tf_disc1')
verifyMinimumPhase(invpendulum_cartpos_tf_disc1,12,4,1,-1,'DFI');
disp('running invpendulum_cartpos_tf_disc2')
verifyMinimumPhase(invpendulum_cartpos_tf_disc2,2,14,1,-1,'DFII');
disp('running invpendulum_cartpos_tf_disc3')
verifyMinimumPhase(invpendulum_cartpos_tf_disc3,10,6,1,-1,'TDFII');
disp('running invpendulum_cartpos_tf_disc4')
verifyMinimumPhase(invpendulum_cartpos_tf_disc4,8,8,1,-1,'DFI');
disp('running invpendulum_cartpos_tf_disc5')
verifyMinimumPhase(invpendulum_cartpos_tf_disc5,6,10,1,-1,'DFII');
disp('running invpendulum_cartpos_tf_disc6')
verifyMinimumPhase(invpendulum_cartpos_tf_disc6,7,9,1,-1,'TDFII');
disp('running invpendulum_cartpos_tf_disc7')
verifyMinimumPhase(invpendulum_cartpos_tf_disc7,9,7,1,-1,'DFI');
disp('running invpendulum_cartpos_tf_disc8')
verifyMinimumPhase(invpendulum_cartpos_tf_disc8,11,5,1,-1,'DFII');

disp('running magsuspension_tf_disc1')
verifyMinimumPhase(magsuspension_tf_disc1,12,4,1,-1,'DFI');
disp('running magsuspension_tf_disc2')
verifyMinimumPhase(magsuspension_tf_disc2,2,14,1,-1,'DFII');
disp('running magsuspension_tf_disc3')
verifyMinimumPhase(magsuspension_tf_disc3,10,6,1,-1,'TDFII');
disp('running magsuspension_tf_disc4')
verifyMinimumPhase(magsuspension_tf_disc4,8,8,1,-1,'DFI');
disp('running magsuspension_tf_disc5')
verifyMinimumPhase(magsuspension_tf_disc5,6,10,1,-1,'DFII');
disp('running magsuspension_tf_disc6')
verifyMinimumPhase(magsuspension_tf_disc6,7,9,1,-1,'TDFII');
disp('running magsuspension_tf_disc7')
verifyMinimumPhase(magsuspension_tf_disc7,9,7,1,-1,'DFI');
disp('running magsuspension_tf_disc8')
verifyMinimumPhase(magsuspension_tf_disc8,11,5,1,-1,'DFII');

disp('running cruise_tf_disc1')
verifyMinimumPhase(cruise_tf_disc1,12,4,1,-1,'DFI');
disp('running cruise_tf_disc2')
verifyMinimumPhase(cruise_tf_disc2,2,14,1,-1,'DFII');
disp('running cruise_tf_disc3')
verifyMinimumPhase(cruise_tf_disc3,10,6,1,-1,'TDFII');
disp('running cruise_tf_disc4')
verifyMinimumPhase(cruise_tf_disc4,8,8,1,-1,'DFI');
disp('running cruise_tf_disc5')
verifyMinimumPhase(cruise_tf_disc5,6,10,1,-1,'DFII');
disp('running cruise_tf_disc6')
verifyMinimumPhase(cruise_tf_disc6,7,9,1,-1,'TDFII');
disp('running cruise_tf_disc7')
verifyMinimumPhase(cruise_tf_disc7,9,7,1,-1,'DFI');

disp('running tapedriver_tf_disc1')
verifyMinimumPhase(tapedriver_tf_disc1,12,4,1,-1,'DFI');
disp('running tapedriver_tf_disc2')
verifyMinimumPhase(tapedriver_tf_disc2,2,14,1,-1,'DFII');
disp('running tapedriver_tf_disc3')
verifyMinimumPhase(tapedriver_tf_disc3,10,6,1,-1,'TDFII');
disp('running tapedriver_tf_disc4')
verifyMinimumPhase(tapedriver_tf_disc4,8,8,1,-1,'DFI');
disp('running tapedriver_tf_disc5')
verifyMinimumPhase(tapedriver_tf_disc5,6,10,1,-1,'DFII');
disp('running tapedriver_tf_disc6')
verifyMinimumPhase(tapedriver_tf_disc6,7,9,1,-1,'TDFII');
disp('running tapedriver_tf_disc7')
verifyMinimumPhase(tapedriver_tf_disc7,9,7,1,-1,'DFI');
disp('running tapedriver_tf_disc8')
verifyMinimumPhase(tapedriver_tf_disc8,11,5,1,-1,'DFII');

disp('running helicopter_tf_disc1')
verifyMinimumPhase(helicopter_tf_disc1,12,4,1,-1,'DFI');
disp('running helicopter_tf_disc2')
verifyMinimumPhase(helicopter_tf_disc2,2,14,1,-1,'DFII');
disp('running helicopter_tf_disc3')
verifyMinimumPhase(helicopter_tf_disc3,10,6,1,-1,'TDFII');
disp('running helicopter_tf_disc4')
verifyMinimumPhase(helicopter_tf_disc4,8,8,1,-1,'DFI');
disp('running helicopter_tf_disc5')
verifyMinimumPhase(helicopter_tf_disc5,6,10,1,-1,'DFII');
disp('running helicopter_tf_disc6')
verifyMinimumPhase(helicopter_tf_disc6,7,9,1,-1,'TDFII');
disp('running helicopter_tf_disc7')
verifyMinimumPhase(helicopter_tf_disc7,9,7,1,-1,'DFI');
disp('running helicopter_tf_disc8')
verifyMinimumPhase(helicopter_tf_disc8,11,5,1,-1,'DFII');

disp('running uscgtampa_tf_disc1')
verifyMinimumPhase(uscgtampa_tf_disc1,12,4,1,-1,'DFI');
disp('running uscgtampa_tf_disc2')
verifyMinimumPhase(uscgtampa_tf_disc2,2,14,1,-1,'DFII');
disp('running uscgtampa_tf_disc3')
verifyMinimumPhase(uscgtampa_tf_disc3,10,6,1,-1,'TDFII');
disp('running uscgtampa_tf_disc4')
verifyMinimumPhase(uscgtampa_tf_disc4,8,8,1,-1,'DFI');
disp('running uscgtampa_tf_disc5')
verifyMinimumPhase(uscgtampa_tf_disc5,6,10,1,-1,'DFII');
disp('running uscgtampa_tf_disc6')
verifyMinimumPhase(uscgtampa_tf_disc6,7,9,1,-1,'TDFII');
disp('running uscgtampa_tf_disc7')
verifyMinimumPhase(uscgtampa_tf_disc7,9,7,1,-1,'DFI');
disp('running uscgtampa_tf_disc8')
verifyMinimumPhase(uscgtampa_tf_disc8,11,5,1,-1,'DFII');

disp('running magneticpointer_tf_disc1')
verifyMinimumPhase(magneticpointer_tf_disc1,12,4,1,-1,'DFI');
disp('running magneticpointer_tf_disc2')
verifyMinimumPhase(magneticpointer_tf_disc2,2,14,1,-1,'DFII');
disp('running magneticpointer_tf_disc3')
verifyMinimumPhase(magneticpointer_tf_disc3,10,6,1,-1,'TDFII');
disp('running magneticpointer_tf_disc4')
verifyMinimumPhase(magneticpointer_tf_disc4,8,8,1,-1,'DFI');
disp('running magneticpointer_tf_disc5')
verifyMinimumPhase(magneticpointer_tf_disc5,6,10,1,-1,'DFII');
disp('running magneticpointer_tf_disc6')
verifyMinimumPhase(magneticpointer_tf_disc6,7,9,1,-1,'TDFII');
disp('running magneticpointer_tf_disc7')
verifyMinimumPhase(magneticpointer_tf_disc7,9,7,1,-1,'DFI');
disp('running magneticpointer_tf_disc8')
verifyMinimumPhase(magneticpointer_tf_disc8,11,5,1,-1,'DFII');
