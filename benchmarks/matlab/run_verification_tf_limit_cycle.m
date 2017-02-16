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
verifyLimitCycle(dcmotor_tf_disc1,12,4,1,-1,'DFI',10);
disp('running dcmotor_tf_disc2')
verifyLimitCycle(dcmotor_tf_disc2,2,14,1,-1,'DFII',10);
disp('running dcmotor_tf_disc3')
verifyLimitCycle(dcmotor_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running dcmotor_tf_disc4')
verifyLimitCycle(dcmotor_tf_disc4,8,8,1,-1,'DFI',10);
disp('running dcmotor_tf_disc5')
verifyLimitCycle(dcmotor_tf_disc5,6,10,1,-1,'DFII',10);
disp('running dcmotor_tf_disc6')
verifyLimitCycle(dcmotor_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running dcmotor_tf_disc7')
verifyLimitCycle(dcmotor_tf_disc7,9,7,1,-1,'DFI',10);
disp('running dcmotor_tf_disc8')
verifyLimitCycle(dcmotor_tf_disc8,11,5,1,-1,'DFII',10);

disp('running pendulum_tf_disc1')
verifyLimitCycle(pendulum_tf_disc1,12,4,1,-1,'DFI',10);
disp('running pendulum_tf_disc2')
verifyLimitCycle(pendulum_tf_disc2,2,14,1,-1,'DFII',10);
disp('running pendulum_tf_disc3')
verifyLimitCycle(pendulum_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running pendulum_tf_disc4')
verifyLimitCycle(pendulum_tf_disc4,8,8,1,-1,'DFI',10);
disp('running pendulum_tf_disc5')
verifyLimitCycle(pendulum_tf_disc5,6,10,1,-1,'DFII',10);
disp('running pendulum_tf_disc6')
verifyLimitCycle(pendulum_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running pendulum_tf_disc7')
verifyLimitCycle(pendulum_tf_disc7,9,7,1,-1,'DFI',10);
disp('running pendulum_tf_disc8')
verifyLimitCycle(pendulum_tf_disc8,11,5,1,-1,'DFII',10);

disp('running invpendulum_cartpos_tf_disc1')
verifyLimitCycle(invpendulum_cartpos_tf_disc1,12,4,1,-1,'DFI',10);
disp('running invpendulum_cartpos_tf_disc2')
verifyLimitCycle(invpendulum_cartpos_tf_disc2,2,14,1,-1,'DFII',10);
disp('running invpendulum_cartpos_tf_disc3')
verifyLimitCycle(invpendulum_cartpos_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running invpendulum_cartpos_tf_disc4')
verifyLimitCycle(invpendulum_cartpos_tf_disc4,8,8,1,-1,'DFI',10);
disp('running invpendulum_cartpos_tf_disc5')
verifyLimitCycle(invpendulum_cartpos_tf_disc5,6,10,1,-1,'DFII',10);
disp('running invpendulum_cartpos_tf_disc6')
verifyLimitCycle(invpendulum_cartpos_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running invpendulum_cartpos_tf_disc7')
verifyLimitCycle(invpendulum_cartpos_tf_disc7,9,7,1,-1,'DFI',10);
disp('running invpendulum_cartpos_tf_disc8')
verifyLimitCycle(invpendulum_cartpos_tf_disc8,11,5,1,-1,'DFII',10);

disp('running magsuspension_tf_disc1')
verifyLimitCycle(magsuspension_tf_disc1,12,4,1,-1,'DFI',10);
disp('running magsuspension_tf_disc2')
verifyLimitCycle(magsuspension_tf_disc2,2,14,1,-1,'DFII',10);
disp('running magsuspension_tf_disc3')
verifyLimitCycle(magsuspension_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running magsuspension_tf_disc4')
verifyLimitCycle(magsuspension_tf_disc4,8,8,1,-1,'DFI',10);
disp('running magsuspension_tf_disc5')
verifyLimitCycle(magsuspension_tf_disc5,6,10,1,-1,'DFII',10);
disp('running magsuspension_tf_disc6')
verifyLimitCycle(magsuspension_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running magsuspension_tf_disc7')
verifyLimitCycle(magsuspension_tf_disc7,9,7,1,-1,'DFI',10);
disp('running magsuspension_tf_disc8')
verifyLimitCycle(magsuspension_tf_disc8,11,5,1,-1,'DFII',10);

disp('running cruise_tf_disc1')
verifyLimitCycle(cruise_tf_disc1,12,4,1,-1,'DFI',10);
disp('running cruise_tf_disc2')
verifyLimitCycle(cruise_tf_disc2,2,14,1,-1,'DFII',10);
disp('running cruise_tf_disc3')
verifyLimitCycle(cruise_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running cruise_tf_disc4')
verifyLimitCycle(cruise_tf_disc4,8,8,1,-1,'DFI',10);
disp('running cruise_tf_disc5')
verifyLimitCycle(cruise_tf_disc5,6,10,1,-1,'DFII',10);
disp('running cruise_tf_disc6')
verifyLimitCycle(cruise_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running cruise_tf_disc7')
verifyLimitCycle(cruise_tf_disc7,9,7,1,-1,'DFI',10);

disp('running tapedriver_tf_disc1')
verifyLimitCycle(tapedriver_tf_disc1,12,4,1,-1,'DFI',10);
disp('running tapedriver_tf_disc2')
verifyLimitCycle(tapedriver_tf_disc2,2,14,1,-1,'DFII',10);
disp('running tapedriver_tf_disc3')
verifyLimitCycle(tapedriver_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running tapedriver_tf_disc4')
verifyLimitCycle(tapedriver_tf_disc4,8,8,1,-1,'DFI',10);
disp('running tapedriver_tf_disc5')
verifyLimitCycle(tapedriver_tf_disc5,6,10,1,-1,'DFII',10);
disp('running tapedriver_tf_disc6')
verifyLimitCycle(tapedriver_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running tapedriver_tf_disc7')
verifyLimitCycle(tapedriver_tf_disc7,9,7,1,-1,'DFI',10);
disp('running tapedriver_tf_disc8')
verifyLimitCycle(tapedriver_tf_disc8,11,5,1,-1,'DFII',10);

disp('running helicopter_tf_disc1')
verifyLimitCycle(helicopter_tf_disc1,12,4,1,-1,'DFI',10);
disp('running helicopter_tf_disc2')
verifyLimitCycle(helicopter_tf_disc2,2,14,1,-1,'DFII',10);
disp('running helicopter_tf_disc3')
verifyLimitCycle(helicopter_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running helicopter_tf_disc4')
verifyLimitCycle(helicopter_tf_disc4,8,8,1,-1,'DFI',10);
disp('running helicopter_tf_disc5')
verifyLimitCycle(helicopter_tf_disc5,6,10,1,-1,'DFII',10);
disp('running helicopter_tf_disc6')
verifyLimitCycle(helicopter_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running helicopter_tf_disc7')
verifyLimitCycle(helicopter_tf_disc7,9,7,1,-1,'DFI',10);
disp('running helicopter_tf_disc8')
verifyLimitCycle(helicopter_tf_disc8,11,5,1,-1,'DFII',10);

disp('running uscgtampa_tf_disc1')
verifyLimitCycle(uscgtampa_tf_disc1,12,4,1,-1,'DFI',10);
disp('running uscgtampa_tf_disc2')
verifyLimitCycle(uscgtampa_tf_disc2,2,14,1,-1,'DFII',10);
disp('running uscgtampa_tf_disc3')
verifyLimitCycle(uscgtampa_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running uscgtampa_tf_disc4')
verifyLimitCycle(uscgtampa_tf_disc4,8,8,1,-1,'DFI',10);
disp('running uscgtampa_tf_disc5')
verifyLimitCycle(uscgtampa_tf_disc5,6,10,1,-1,'DFII',10);
disp('running uscgtampa_tf_disc6')
verifyLimitCycle(uscgtampa_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running uscgtampa_tf_disc7')
verifyLimitCycle(uscgtampa_tf_disc7,9,7,1,-1,'DFI',10);
disp('running uscgtampa_tf_disc8')
verifyLimitCycle(uscgtampa_tf_disc8,11,5,1,-1,'DFII',10);

disp('running magneticpointer_tf_disc1')
verifyLimitCycle(magneticpointer_tf_disc1,12,4,1,-1,'DFI',10);
disp('running magneticpointer_tf_disc2')
verifyLimitCycle(magneticpointer_tf_disc2,2,14,1,-1,'DFII',10);
disp('running magneticpointer_tf_disc3')
verifyLimitCycle(magneticpointer_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running magneticpointer_tf_disc4')
verifyLimitCycle(magneticpointer_tf_disc4,8,8,1,-1,'DFI',10);
disp('running magneticpointer_tf_disc5')
verifyLimitCycle(magneticpointer_tf_disc5,6,10,1,-1,'DFII',10);
disp('running magneticpointer_tf_disc6')
verifyLimitCycle(magneticpointer_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running magneticpointer_tf_disc7')
verifyLimitCycle(magneticpointer_tf_disc7,9,7,1,-1,'DFI',10);
disp('running magneticpointer_tf_disc8')
verifyLimitCycle(magneticpointer_tf_disc8,11,5,1,-1,'DFII',10);
