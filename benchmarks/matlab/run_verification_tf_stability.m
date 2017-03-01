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
verifyStability(dcmotor_tf_disc1,12,4,1,-1,'DFI');
disp('running dcmotor_tf_disc2')
verifyStability(dcmotor_tf_disc2,2,14,1,-1,'DFII');
disp('running dcmotor_tf_disc3')
verifyStability(dcmotor_tf_disc3,10,6,1,-1,'TDFII');
disp('running dcmotor_tf_disc4')
verifyStability(dcmotor_tf_disc4,8,8,1,-1,'DFI');
disp('running dcmotor_tf_disc5')
verifyStability(dcmotor_tf_disc5,6,10,1,-1,'DFII');
disp('running dcmotor_tf_disc6')
verifyStability(dcmotor_tf_disc6,7,9,1,-1,'TDFII');
disp('running dcmotor_tf_disc7')
verifyStability(dcmotor_tf_disc7,9,7,1,-1,'DFI');
disp('running dcmotor_tf_disc8')
verifyStability(dcmotor_tf_disc8,11,5,1,-1,'DFII');

disp('running pendulum_tf_disc1')
verifyStability(pendulum_tf_disc1,12,4,1,-1,'DFI');
disp('running pendulum_tf_disc2')
verifyStability(pendulum_tf_disc2,2,14,1,-1,'DFII');
disp('running pendulum_tf_disc3')
verifyStability(pendulum_tf_disc3,10,6,1,-1,'TDFII');
disp('running pendulum_tf_disc4')
verifyStability(pendulum_tf_disc4,8,8,1,-1,'DFI');
disp('running pendulum_tf_disc5')
verifyStability(pendulum_tf_disc5,6,10,1,-1,'DFII');
disp('running pendulum_tf_disc6')
verifyStability(pendulum_tf_disc6,7,9,1,-1,'TDFII');
disp('running pendulum_tf_disc7')
verifyStability(pendulum_tf_disc7,9,7,1,-1,'DFI');
disp('running pendulum_tf_disc8')
verifyStability(pendulum_tf_disc8,11,5,1,-1,'DFII');

disp('running invpendulum_cartpos_tf_disc1')
verifyStability(invpendulum_cartpos_tf_disc1,12,4,1,-1,'DFI');
disp('running invpendulum_cartpos_tf_disc2')
verifyStability(invpendulum_cartpos_tf_disc2,2,14,1,-1,'DFII');
disp('running invpendulum_cartpos_tf_disc3')
verifyStability(invpendulum_cartpos_tf_disc3,10,6,1,-1,'TDFII');
disp('running invpendulum_cartpos_tf_disc4')
verifyStability(invpendulum_cartpos_tf_disc4,8,8,1,-1,'DFI');
disp('running invpendulum_cartpos_tf_disc5')
verifyStability(invpendulum_cartpos_tf_disc5,6,10,1,-1,'DFII');
disp('running invpendulum_cartpos_tf_disc6')
verifyStability(invpendulum_cartpos_tf_disc6,7,9,1,-1,'TDFII');
disp('running invpendulum_cartpos_tf_disc7')
verifyStability(invpendulum_cartpos_tf_disc7,9,7,1,-1,'DFI');
disp('running invpendulum_cartpos_tf_disc8')
verifyStability(invpendulum_cartpos_tf_disc8,11,5,1,-1,'DFII');

disp('running magsuspension_tf_disc1')
verifyStability(magsuspension_tf_disc1,12,4,1,-1,'DFI');
disp('running magsuspension_tf_disc2')
verifyStability(magsuspension_tf_disc2,2,14,1,-1,'DFII');
disp('running magsuspension_tf_disc3')
verifyStability(magsuspension_tf_disc3,10,6,1,-1,'TDFII');
disp('running magsuspension_tf_disc4')
verifyStability(magsuspension_tf_disc4,8,8,1,-1,'DFI');
disp('running magsuspension_tf_disc5')
verifyStability(magsuspension_tf_disc5,6,10,1,-1,'DFII');
disp('running magsuspension_tf_disc6')
verifyStability(magsuspension_tf_disc6,7,9,1,-1,'TDFII');
disp('running magsuspension_tf_disc7')
verifyStability(magsuspension_tf_disc7,9,7,1,-1,'DFI');
disp('running magsuspension_tf_disc8')
verifyStability(magsuspension_tf_disc8,11,5,1,-1,'DFII');

disp('running cruise_tf_disc1')
verifyStability(cruise_tf_disc1,12,4,1,-1,'DFI');
disp('running cruise_tf_disc2')
verifyStability(cruise_tf_disc2,2,14,1,-1,'DFII');
disp('running cruise_tf_disc3')
verifyStability(cruise_tf_disc3,10,6,1,-1,'TDFII');
disp('running cruise_tf_disc4')
verifyStability(cruise_tf_disc4,8,8,1,-1,'DFI');
disp('running cruise_tf_disc5')
verifyStability(cruise_tf_disc5,6,10,1,-1,'DFII');
disp('running cruise_tf_disc6')
verifyStability(cruise_tf_disc6,7,9,1,-1,'TDFII');
disp('running cruise_tf_disc7')
verifyStability(cruise_tf_disc7,9,7,1,-1,'DFI');

disp('running tapedriver_tf_disc1')
verifyStability(tapedriver_tf_disc1,12,4,1,-1,'DFI');
disp('running tapedriver_tf_disc2')
verifyStability(tapedriver_tf_disc2,2,14,1,-1,'DFII');
disp('running tapedriver_tf_disc3')
verifyStability(tapedriver_tf_disc3,10,6,1,-1,'TDFII');
disp('running tapedriver_tf_disc4')
verifyStability(tapedriver_tf_disc4,8,8,1,-1,'DFI');
disp('running tapedriver_tf_disc5')
verifyStability(tapedriver_tf_disc5,6,10,1,-1,'DFII');
disp('running tapedriver_tf_disc6')
verifyStability(tapedriver_tf_disc6,7,9,1,-1,'TDFII');
disp('running tapedriver_tf_disc7')
verifyStability(tapedriver_tf_disc7,9,7,1,-1,'DFI');
disp('running tapedriver_tf_disc8')
verifyStability(tapedriver_tf_disc8,11,5,1,-1,'DFII');

disp('running helicopter_tf_disc1')
verifyStability(helicopter_tf_disc1,12,4,1,-1,'DFI');
disp('running helicopter_tf_disc2')
verifyStability(helicopter_tf_disc2,2,14,1,-1,'DFII');
disp('running helicopter_tf_disc3')
verifyStability(helicopter_tf_disc3,10,6,1,-1,'TDFII');
disp('running helicopter_tf_disc4')
verifyStability(helicopter_tf_disc4,8,8,1,-1,'DFI');
disp('running helicopter_tf_disc5')
verifyStability(helicopter_tf_disc5,6,10,1,-1,'DFII');
disp('running helicopter_tf_disc6')
verifyStability(helicopter_tf_disc6,7,9,1,-1,'TDFII');
disp('running helicopter_tf_disc7')
verifyStability(helicopter_tf_disc7,9,7,1,-1,'DFI');
disp('running helicopter_tf_disc8')
verifyStability(helicopter_tf_disc8,11,5,1,-1,'DFII');

disp('running uscgtampa_tf_disc1')
verifyStability(uscgtampa_tf_disc1,12,4,1,-1,'DFI');
disp('running uscgtampa_tf_disc2')
verifyStability(uscgtampa_tf_disc2,2,14,1,-1,'DFII');
disp('running uscgtampa_tf_disc3')
verifyStability(uscgtampa_tf_disc3,10,6,1,-1,'TDFII');
disp('running uscgtampa_tf_disc4')
verifyStability(uscgtampa_tf_disc4,8,8,1,-1,'DFI');
disp('running uscgtampa_tf_disc5')
verifyStability(uscgtampa_tf_disc5,6,10,1,-1,'DFII');
disp('running uscgtampa_tf_disc6')
verifyStability(uscgtampa_tf_disc6,7,9,1,-1,'TDFII');
disp('running uscgtampa_tf_disc7')
verifyStability(uscgtampa_tf_disc7,9,7,1,-1,'DFI');
disp('running uscgtampa_tf_disc8')
verifyStability(uscgtampa_tf_disc8,11,5,1,-1,'DFII');

disp('running magneticpointer_tf_disc1')
verifyStability(magneticpointer_tf_disc1,12,4,1,-1,'DFI');
disp('running magneticpointer_tf_disc2')
verifyStability(magneticpointer_tf_disc2,2,14,1,-1,'DFII');
disp('running magneticpointer_tf_disc3')
verifyStability(magneticpointer_tf_disc3,10,6,1,-1,'TDFII');
disp('running magneticpointer_tf_disc4')
verifyStability(magneticpointer_tf_disc4,8,8,1,-1,'DFI');
disp('running magneticpointer_tf_disc5')
verifyStability(magneticpointer_tf_disc5,6,10,1,-1,'DFII');
disp('running magneticpointer_tf_disc6')
verifyStability(magneticpointer_tf_disc6,7,9,1,-1,'TDFII');
disp('running magneticpointer_tf_disc7')
verifyStability(magneticpointer_tf_disc7,9,7,1,-1,'DFI');
disp('running magneticpointer_tf_disc8')
verifyStability(magneticpointer_tf_disc8,11,5,1,-1,'DFII');
