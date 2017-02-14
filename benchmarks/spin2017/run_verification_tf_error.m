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
verifyError(dcmotor_tf_disc1,12,4,1,-1,'DFI', 10, 0.18);
disp('running dcmotor_tf_disc2')
verifyError(dcmotor_tf_disc2,2,14,1,-1,'DFII', 10, 0.18);
disp('running dcmotor_tf_disc3')
verifyError(dcmotor_tf_disc3,10,6,1,-1,'TDFII', 10, 0.18);
disp('running dcmotor_tf_disc4')
verifyError(dcmotor_tf_disc4,8,8,1,-1,'DFI', 10, 0.18);
disp('running dcmotor_tf_disc5')
verifyError(dcmotor_tf_disc5,6,10,1,-1,'DFII', 10, 0.18);
disp('running dcmotor_tf_disc6')
verifyError(dcmotor_tf_disc6,7,9,1,-1,'TDFII', 10, 0.18);
disp('running dcmotor_tf_disc7')
verifyError(dcmotor_tf_disc7,9,7,1,-1,'DFI', 10, 0.18);
disp('running dcmotor_tf_disc8')
verifyError(dcmotor_tf_disc8,11,5,1,-1,'DFII', 10, 0.18);

disp('running pendulum_tf_disc1')
verifyError(pendulum_tf_disc1,12,4,1,-1,'DFI', 10, 0.18);
disp('running pendulum_tf_disc2')
verifyError(pendulum_tf_disc2,2,14,1,-1,'DFII', 10, 0.18);
disp('running pendulum_tf_disc3')
verifyError(pendulum_tf_disc3,10,6,1,-1,'TDFII', 10, 0.18);
disp('running pendulum_tf_disc4')
verifyError(pendulum_tf_disc4,8,8,1,-1,'DFI', 10, 0.18);
disp('running pendulum_tf_disc5')
verifyError(pendulum_tf_disc5,6,10,1,-1,'DFII', 10, 0.18);
disp('running pendulum_tf_disc6')
verifyError(pendulum_tf_disc6,7,9,1,-1,'TDFII', 10, 0.18);
disp('running pendulum_tf_disc7')
verifyError(pendulum_tf_disc7,9,7,1,-1,'DFI', 10, 0.18);
disp('running pendulum_tf_disc8')
verifyError(pendulum_tf_disc8,11,5,1,-1,'DFII', 10, 0.18);

disp('running invpendulum_cartpos_tf_disc1')
verifyError(invpendulum_cartpos_tf_disc1,12,4,1,-1,'DFI', 10, 0.18);
disp('running invpendulum_cartpos_tf_disc2')
verifyError(invpendulum_cartpos_tf_disc2,2,14,1,-1,'DFII', 10, 0.18);
disp('running invpendulum_cartpos_tf_disc3')
verifyError(invpendulum_cartpos_tf_disc3,10,6,1,-1,'TDFII', 10, 0.18);
disp('running invpendulum_cartpos_tf_disc4')
verifyError(invpendulum_cartpos_tf_disc4,8,8,1,-1,'DFI', 10, 0.18);
disp('running invpendulum_cartpos_tf_disc5')
verifyError(invpendulum_cartpos_tf_disc5,6,10,1,-1,'DFII', 10, 0.18);
disp('running invpendulum_cartpos_tf_disc6')
verifyError(invpendulum_cartpos_tf_disc6,7,9,1,-1,'TDFII', 10, 0.18);
disp('running invpendulum_cartpos_tf_disc7')
verifyError(invpendulum_cartpos_tf_disc7,9,7,1,-1,'DFI', 10, 0.18);
disp('running invpendulum_cartpos_tf_disc8')
verifyError(invpendulum_cartpos_tf_disc8,11,5,1,-1,'DFII', 10, 0.18);

disp('running magsuspension_tf_disc1')
verifyError(magsuspension_tf_disc1,12,4,1,-1,'DFI', 10, 0.18);
disp('running magsuspension_tf_disc2')
verifyError(magsuspension_tf_disc2,2,14,1,-1,'DFII', 10, 0.18);
disp('running magsuspension_tf_disc3')
verifyError(magsuspension_tf_disc3,10,6,1,-1,'TDFII', 10, 0.18);
disp('running magsuspension_tf_disc4')
verifyError(magsuspension_tf_disc4,8,8,1,-1,'DFI', 10, 0.18);
disp('running magsuspension_tf_disc5')
verifyError(magsuspension_tf_disc5,6,10,1,-1,'DFII', 10, 0.18);
disp('running magsuspension_tf_disc6')
verifyError(magsuspension_tf_disc6,7,9,1,-1,'TDFII', 10, 0.18);
disp('running magsuspension_tf_disc7')
verifyError(magsuspension_tf_disc7,9,7,1,-1,'DFI', 10, 0.18);
disp('running magsuspension_tf_disc8')
verifyError(magsuspension_tf_disc8,11,5,1,-1,'DFII', 10, 0.18);

disp('running cruise_tf_disc1')
verifyError(cruise_tf_disc1,12,4,1,-1,'DFI', 10, 0.18);
disp('running cruise_tf_disc2')
verifyError(cruise_tf_disc2,2,14,1,-1,'DFII', 10, 0.18);
disp('running cruise_tf_disc3')
verifyError(cruise_tf_disc3,10,6,1,-1,'TDFII', 10, 0.18);
disp('running cruise_tf_disc4')
verifyError(cruise_tf_disc4,8,8,1,-1,'DFI', 10, 0.18);
disp('running cruise_tf_disc5')
verifyError(cruise_tf_disc5,6,10,1,-1,'DFII', 10, 0.18);
disp('running cruise_tf_disc6')
verifyError(cruise_tf_disc6,7,9,1,-1,'TDFII', 10, 0.18);
disp('running cruise_tf_disc7')
verifyError(cruise_tf_disc7,9,7,1,-1,'DFI', 10, 0.18);

disp('running tapedriver_tf_disc1')
verifyError(tapedriver_tf_disc1,12,4,1,-1,'DFI', 10, 0.18);
disp('running tapedriver_tf_disc2')
verifyError(tapedriver_tf_disc2,2,14,1,-1,'DFII', 10, 0.18);
disp('running tapedriver_tf_disc3')
verifyError(tapedriver_tf_disc3,10,6,1,-1,'TDFII', 10, 0.18);
disp('running tapedriver_tf_disc4')
verifyError(tapedriver_tf_disc4,8,8,1,-1,'DFI', 10, 0.18);
disp('running tapedriver_tf_disc5')
verifyError(tapedriver_tf_disc5,6,10,1,-1,'DFII', 10, 0.18);
disp('running tapedriver_tf_disc6')
verifyError(tapedriver_tf_disc6,7,9,1,-1,'TDFII', 10, 0.18);
disp('running tapedriver_tf_disc7')
verifyError(tapedriver_tf_disc7,9,7,1,-1,'DFI', 10, 0.18);
disp('running tapedriver_tf_disc8')
verifyError(tapedriver_tf_disc8,11,5,1,-1,'DFII', 10, 0.18);

disp('running helicopter_tf_disc1')
verifyError(helicopter_tf_disc1,12,4,1,-1,'DFI', 10, 0.18);
disp('running helicopter_tf_disc2')
verifyError(helicopter_tf_disc2,2,14,1,-1,'DFII', 10, 0.18);
disp('running helicopter_tf_disc3')
verifyError(helicopter_tf_disc3,10,6,1,-1,'TDFII', 10, 0.18);
disp('running helicopter_tf_disc4')
verifyError(helicopter_tf_disc4,8,8,1,-1,'DFI', 10, 0.18);
disp('running helicopter_tf_disc5')
verifyError(helicopter_tf_disc5,6,10,1,-1,'DFII', 10, 0.18);
disp('running helicopter_tf_disc6')
verifyError(helicopter_tf_disc6,7,9,1,-1,'TDFII', 10, 0.18);
disp('running helicopter_tf_disc7')
verifyError(helicopter_tf_disc7,9,7,1,-1,'DFI', 10, 0.18);
disp('running helicopter_tf_disc8')
verifyError(helicopter_tf_disc8,11,5,1,-1,'DFII', 10, 0.18);

disp('running uscgtampa_tf_disc1')
verifyError(uscgtampa_tf_disc1,12,4,1,-1,'DFI', 10, 0.18);
disp('running uscgtampa_tf_disc2')
verifyError(uscgtampa_tf_disc2,2,14,1,-1,'DFII', 10, 0.18);
disp('running uscgtampa_tf_disc3')
verifyError(uscgtampa_tf_disc3,10,6,1,-1,'TDFII', 10, 0.18);
disp('running uscgtampa_tf_disc4')
verifyError(uscgtampa_tf_disc4,8,8,1,-1,'DFI', 10, 0.18);
disp('running uscgtampa_tf_disc5')
verifyError(uscgtampa_tf_disc5,6,10,1,-1,'DFII', 10, 0.18);
disp('running uscgtampa_tf_disc6')
verifyError(uscgtampa_tf_disc6,7,9,1,-1,'TDFII', 10, 0.18);
disp('running uscgtampa_tf_disc7')
verifyError(uscgtampa_tf_disc7,9,7,1,-1,'DFI', 10, 0.18);
disp('running uscgtampa_tf_disc8')
verifyError(uscgtampa_tf_disc8,11,5,1,-1,'DFII', 10, 0.18);

disp('running magneticpointer_tf_disc1')
verifyError(magneticpointer_tf_disc1,12,4,1,-1,'DFI', 10, 0.18);
disp('running magneticpointer_tf_disc2')
verifyError(magneticpointer_tf_disc2,2,14,1,-1,'DFII', 10, 0.18);
disp('running magneticpointer_tf_disc3')
verifyError(magneticpointer_tf_disc3,10,6,1,-1,'TDFII', 10, 0.18);
disp('running magneticpointer_tf_disc4')
verifyError(magneticpointer_tf_disc4,8,8,1,-1,'DFI', 10, 0.18);
disp('running magneticpointer_tf_disc5')
verifyError(magneticpointer_tf_disc5,6,10,1,-1,'DFII', 10, 0.18);
disp('running magneticpointer_tf_disc6')
verifyError(magneticpointer_tf_disc6,7,9,1,-1,'TDFII', 10, 0.18);
disp('running magneticpointer_tf_disc7')
verifyError(magneticpointer_tf_disc7,9,7,1,-1,'DFI', 10, 0.18);
disp('running magneticpointer_tf_disc8')
verifyError(magneticpointer_tf_disc8,11,5,1,-1,'DFII', 10, 0.18);
