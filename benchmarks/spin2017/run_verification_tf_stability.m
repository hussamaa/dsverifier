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

verifyStability(dcmotor_tf_disc1,12,4,1,-1,'DFI');
verifyStability(dcmotor_tf_disc2,2,14,1,-1,'DFII');
verifyStability(dcmotor_tf_disc3,10,6,1,-1,'TDFII');
verifyStability(dcmotor_tf_disc4,8,8,1,-1,'DFI');
verifyStability(dcmotor_tf_disc5,6,10,1,-1,'DFII');
verifyStability(dcmotor_tf_disc6,7,9,1,-1,'TDFII');
verifyStability(dcmotor_tf_disc7,9,7,1,-1,'DFI');
verifyStability(dcmotor_tf_disc8,11,5,1,-1,'DFII');

verifyStability(pendulum_tf_disc1,12,4,1,-1,'DFI');
verifyStability(pendulum_tf_disc2,2,14,1,-1,'DFII');
verifyStability(pendulum_tf_disc3,10,6,1,-1,'TDFII');
verifyStability(pendulum_tf_disc4,8,8,1,-1,'DFI');
verifyStability(pendulum_tf_disc5,6,10,1,-1,'DFII');
verifyStability(pendulum_tf_disc6,7,9,1,-1,'TDFII');
verifyStability(pendulum_tf_disc7,9,7,1,-1,'DFI');
verifyStability(pendulum_tf_disc8,11,5,1,-1,'DFII');

verifyStability(invpendulum_cartpos_tf_disc1,12,4,1,-1,'DFI');
verifyStability(invpendulum_cartpos_tf_disc2,2,14,1,-1,'DFII');
verifyStability(invpendulum_cartpos_tf_disc3,10,6,1,-1,'TDFII');
verifyStability(invpendulum_cartpos_tf_disc4,8,8,1,-1,'DFI');
verifyStability(invpendulum_cartpos_tf_disc5,6,10,1,-1,'DFII');
verifyStability(invpendulum_cartpos_tf_disc6,7,9,1,-1,'TDFII');
verifyStability(invpendulum_cartpos_tf_disc7,9,7,1,-1,'DFI');
verifyStability(invpendulum_cartpos_tf_disc8,11,5,1,-1,'DFII');

verifyStability(magsuspension_tf_disc1,12,4,1,-1,'DFI');
verifyStability(magsuspension_tf_disc2,2,14,1,-1,'DFII');
verifyStability(magsuspension_tf_disc3,10,6,1,-1,'TDFII');
verifyStability(magsuspension_tf_disc4,8,8,1,-1,'DFI');
verifyStability(magsuspension_tf_disc5,6,10,1,-1,'DFII');
verifyStability(magsuspension_tf_disc6,7,9,1,-1,'TDFII');
verifyStability(magsuspension_tf_disc7,9,7,1,-1,'DFI');
verifyStability(magsuspension_tf_disc8,11,5,1,-1,'DFII');

verifyStability(cruise_tf_disc1,12,4,1,-1,'DFI');
verifyStability(cruise_tf_disc2,2,14,1,-1,'DFII');
verifyStability(cruise_tf_disc3,10,6,1,-1,'TDFII');
verifyStability(cruise_tf_disc4,8,8,1,-1,'DFI');
verifyStability(cruise_tf_disc5,6,10,1,-1,'DFII');
verifyStability(cruise_tf_disc6,7,9,1,-1,'TDFII');
verifyStability(cruise_tf_disc7,9,7,1,-1,'DFI');

verifyStability(tapedriver_tf_disc1,12,4,1,-1,'DFI');
verifyStability(tapedriver_tf_disc2,2,14,1,-1,'DFII');
verifyStability(tapedriver_tf_disc3,10,6,1,-1,'TDFII');
verifyStability(tapedriver_tf_disc4,8,8,1,-1,'DFI');
verifyStability(tapedriver_tf_disc5,6,10,1,-1,'DFII');
verifyStability(tapedriver_tf_disc6,7,9,1,-1,'TDFII');
verifyStability(tapedriver_tf_disc7,9,7,1,-1,'DFI');
verifyStability(tapedriver_tf_disc8,11,5,1,-1,'DFII');

verifyStability(helicopter_tf_disc1,12,4,1,-1,'DFI');
verifyStability(helicopter_tf_disc2,2,14,1,-1,'DFII');
verifyStability(helicopter_tf_disc3,10,6,1,-1,'TDFII');
verifyStability(helicopter_tf_disc4,8,8,1,-1,'DFI');
verifyStability(helicopter_tf_disc5,6,10,1,-1,'DFII');
verifyStability(helicopter_tf_disc6,7,9,1,-1,'TDFII');
verifyStability(helicopter_tf_disc7,9,7,1,-1,'DFI');
verifyStability(helicopter_tf_disc8,11,5,1,-1,'DFII');

verifyStability(uscgtampa_tf_disc1,12,4,1,-1,'DFI');
verifyStability(uscgtampa_tf_disc2,2,14,1,-1,'DFII');
verifyStability(uscgtampa_tf_disc3,10,6,1,-1,'TDFII');
verifyStability(uscgtampa_tf_disc4,8,8,1,-1,'DFI');
verifyStability(uscgtampa_tf_disc5,6,10,1,-1,'DFII');
verifyStability(uscgtampa_tf_disc6,7,9,1,-1,'TDFII');
verifyStability(uscgtampa_tf_disc7,9,7,1,-1,'DFI');
verifyStability(uscgtampa_tf_disc8,11,5,1,-1,'DFII');

verifyStability(magneticpointer_tf_disc1,12,4,1,-1,'DFI');
verifyStability(magneticpointer_tf_disc2,2,14,1,-1,'DFII');
verifyStability(magneticpointer_tf_disc3,10,6,1,-1,'TDFII');
verifyStability(magneticpointer_tf_disc4,8,8,1,-1,'DFI');
verifyStability(magneticpointer_tf_disc5,6,10,1,-1,'DFII');
verifyStability(magneticpointer_tf_disc6,7,9,1,-1,'TDFII');
verifyStability(magneticpointer_tf_disc7,9,7,1,-1,'DFI');
verifyStability(magneticpointer_tf_disc8,11,5,1,-1,'DFII');
