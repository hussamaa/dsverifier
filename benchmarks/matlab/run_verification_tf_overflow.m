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
verifyOverflow(dcmotor_tf_disc1,12,4,1,-1,'DFI',10);
disp('running dcmotor_tf_disc2')
verifyOverflow(dcmotor_tf_disc2,2,14,1,-1,'DFII',10);
disp('running dcmotor_tf_disc3')
verifyOverflow(dcmotor_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running dcmotor_tf_disc4')
verifyOverflow(dcmotor_tf_disc4,8,8,1,-1,'DFI',10);
disp('running dcmotor_tf_disc5')
verifyOverflow(dcmotor_tf_disc5,6,10,1,-1,'DFII',10);
disp('running dcmotor_tf_disc6')
verifyOverflow(dcmotor_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running dcmotor_tf_disc7')
verifyOverflow(dcmotor_tf_disc7,9,7,1,-1,'DFI',10);
disp('running dcmotor_tf_disc8')
verifyOverflow(dcmotor_tf_disc8,11,5,1,-1,'DFII',10);

disp('running pendulum_tf_disc1')
verifyOverflow(pendulum_tf_disc1,12,4,1,-1,'DFI',10);
disp('running pendulum_tf_disc2')
verifyOverflow(pendulum_tf_disc2,2,14,1,-1,'DFII',10);
disp('running pendulum_tf_disc3')
verifyOverflow(pendulum_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running pendulum_tf_disc4')
verifyOverflow(pendulum_tf_disc4,8,8,1,-1,'DFI',10);
disp('running pendulum_tf_disc5')
verifyOverflow(pendulum_tf_disc5,6,10,1,-1,'DFII',10);
disp('running pendulum_tf_disc6')
verifyOverflow(pendulum_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running pendulum_tf_disc7')
verifyOverflow(pendulum_tf_disc7,9,7,1,-1,'DFI',10);
disp('running pendulum_tf_disc8')
verifyOverflow(pendulum_tf_disc8,11,5,1,-1,'DFII',10);

disp('running invpendulum_cartpos_tf_disc1')
verifyOverflow(invpendulum_cartpos_tf_disc1,12,4,1,-1,'DFI',10);
disp('running invpendulum_cartpos_tf_disc2')
verifyOverflow(invpendulum_cartpos_tf_disc2,2,14,1,-1,'DFII',10);
disp('running invpendulum_cartpos_tf_disc3')
verifyOverflow(invpendulum_cartpos_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running invpendulum_cartpos_tf_disc4')
verifyOverflow(invpendulum_cartpos_tf_disc4,8,8,1,-1,'DFI',10);
disp('running invpendulum_cartpos_tf_disc5')
verifyOverflow(invpendulum_cartpos_tf_disc5,6,10,1,-1,'DFII',10);
disp('running invpendulum_cartpos_tf_disc6')
verifyOverflow(invpendulum_cartpos_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running invpendulum_cartpos_tf_disc7')
verifyOverflow(invpendulum_cartpos_tf_disc7,9,7,1,-1,'DFI',10);
disp('running invpendulum_cartpos_tf_disc8')
verifyOverflow(invpendulum_cartpos_tf_disc8,11,5,1,-1,'DFII',10);

disp('running magsuspension_tf_disc1')
verifyOverflow(magsuspension_tf_disc1,12,4,1,-1,'DFI',10);
disp('running magsuspension_tf_disc2')
verifyOverflow(magsuspension_tf_disc2,2,14,1,-1,'DFII',10);
disp('running magsuspension_tf_disc3')
verifyOverflow(magsuspension_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running magsuspension_tf_disc4')
verifyOverflow(magsuspension_tf_disc4,8,8,1,-1,'DFI',10);
disp('running magsuspension_tf_disc5')
verifyOverflow(magsuspension_tf_disc5,6,10,1,-1,'DFII',10);
disp('running magsuspension_tf_disc6')
verifyOverflow(magsuspension_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running magsuspension_tf_disc7')
verifyOverflow(magsuspension_tf_disc7,9,7,1,-1,'DFI',10);
disp('running magsuspension_tf_disc8')
verifyOverflow(magsuspension_tf_disc8,11,5,1,-1,'DFII',10);

disp('running cruise_tf_disc1')
verifyOverflow(cruise_tf_disc1,12,4,1,-1,'DFI',10);
disp('running cruise_tf_disc2')
verifyOverflow(cruise_tf_disc2,2,14,1,-1,'DFII',10);
disp('running cruise_tf_disc3')
verifyOverflow(cruise_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running cruise_tf_disc4')
verifyOverflow(cruise_tf_disc4,8,8,1,-1,'DFI',10);
disp('running cruise_tf_disc5')
verifyOverflow(cruise_tf_disc5,6,10,1,-1,'DFII',10);
disp('running cruise_tf_disc6')
verifyOverflow(cruise_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running cruise_tf_disc7')
verifyOverflow(cruise_tf_disc7,9,7,1,-1,'DFI',10);

disp('running tapedriver_tf_disc1')
verifyOverflow(tapedriver_tf_disc1,12,4,1,-1,'DFI',10);
disp('running tapedriver_tf_disc2')
verifyOverflow(tapedriver_tf_disc2,2,14,1,-1,'DFII',10);
disp('running tapedriver_tf_disc3')
verifyOverflow(tapedriver_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running tapedriver_tf_disc4')
verifyOverflow(tapedriver_tf_disc4,8,8,1,-1,'DFI',10);
disp('running tapedriver_tf_disc5')
verifyOverflow(tapedriver_tf_disc5,6,10,1,-1,'DFII',10);
disp('running tapedriver_tf_disc6')
verifyOverflow(tapedriver_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running tapedriver_tf_disc7')
verifyOverflow(tapedriver_tf_disc7,9,7,1,-1,'DFI',10);
disp('running tapedriver_tf_disc8')
verifyOverflow(tapedriver_tf_disc8,11,5,1,-1,'DFII',10);

disp('running helicopter_tf_disc1')
verifyOverflow(helicopter_tf_disc1,12,4,1,-1,'DFI',10);
disp('running helicopter_tf_disc2')
verifyOverflow(helicopter_tf_disc2,2,14,1,-1,'DFII',10);
disp('running helicopter_tf_disc3')
verifyOverflow(helicopter_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running helicopter_tf_disc4')
verifyOverflow(helicopter_tf_disc4,8,8,1,-1,'DFI',10);
disp('running helicopter_tf_disc5')
verifyOverflow(helicopter_tf_disc5,6,10,1,-1,'DFII',10);
disp('running helicopter_tf_disc6')
verifyOverflow(helicopter_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running helicopter_tf_disc7')
verifyOverflow(helicopter_tf_disc7,9,7,1,-1,'DFI',10);
disp('running helicopter_tf_disc8')
verifyOverflow(helicopter_tf_disc8,11,5,1,-1,'DFII',10);

disp('running uscgtampa_tf_disc1')
verifyOverflow(uscgtampa_tf_disc1,12,4,1,-1,'DFI',10);
disp('running uscgtampa_tf_disc2')
verifyOverflow(uscgtampa_tf_disc2,2,14,1,-1,'DFII',10);
disp('running uscgtampa_tf_disc3')
verifyOverflow(uscgtampa_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running uscgtampa_tf_disc4')
verifyOverflow(uscgtampa_tf_disc4,8,8,1,-1,'DFI',10);
disp('running uscgtampa_tf_disc5')
verifyOverflow(uscgtampa_tf_disc5,6,10,1,-1,'DFII',10);
disp('running uscgtampa_tf_disc6')
verifyOverflow(uscgtampa_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running uscgtampa_tf_disc7')
verifyOverflow(uscgtampa_tf_disc7,9,7,1,-1,'DFI',10);
disp('running uscgtampa_tf_disc8')
verifyOverflow(uscgtampa_tf_disc8,11,5,1,-1,'DFII',10);

disp('running magneticpointer_tf_disc1')
verifyOverflow(magneticpointer_tf_disc1,12,4,1,-1,'DFI',10);
disp('running magneticpointer_tf_disc2')
verifyOverflow(magneticpointer_tf_disc2,2,14,1,-1,'DFII',10);
disp('running magneticpointer_tf_disc3')
verifyOverflow(magneticpointer_tf_disc3,10,6,1,-1,'TDFII',10);
disp('running magneticpointer_tf_disc4')
verifyOverflow(magneticpointer_tf_disc4,8,8,1,-1,'DFI',10);
disp('running magneticpointer_tf_disc5')
verifyOverflow(magneticpointer_tf_disc5,6,10,1,-1,'DFII',10);
disp('running magneticpointer_tf_disc6')
verifyOverflow(magneticpointer_tf_disc6,7,9,1,-1,'TDFII',10);
disp('running magneticpointer_tf_disc7')
verifyOverflow(magneticpointer_tf_disc7,9,7,1,-1,'DFI',10);
disp('running magneticpointer_tf_disc8')
verifyOverflow(magneticpointer_tf_disc8,11,5,1,-1,'DFII',10);
