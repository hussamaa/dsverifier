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

verifyMinimumPhase(dcmotor_tf_disc1,12,4,1,-1,'DFI');
verifyMinimumPhase(dcmotor_tf_disc2,2,14,1,-1,'DFII');
verifyMinimumPhase(dcmotor_tf_disc3,10,6,1,-1,'TDFII');
verifyMinimumPhase(dcmotor_tf_disc4,8,8,1,-1,'DFI');
verifyMinimumPhase(dcmotor_tf_disc5,6,10,1,-1,'DFII');
verifyMinimumPhase(dcmotor_tf_disc6,7,9,1,-1,'TDFII');
verifyMinimumPhase(dcmotor_tf_disc7,9,7,1,-1,'DFI');
verifyMinimumPhase(dcmotor_tf_disc8,11,5,1,-1,'DFII');

verifyMinimumPhase(pendulum_tf_disc1,12,4,1,-1,'DFI');
verifyMinimumPhase(pendulum_tf_disc2,2,14,1,-1,'DFII');
verifyMinimumPhase(pendulum_tf_disc3,10,6,1,-1,'TDFII');
verifyMinimumPhase(pendulum_tf_disc4,8,8,1,-1,'DFI');
verifyMinimumPhase(pendulum_tf_disc5,6,10,1,-1,'DFII');
verifyMinimumPhase(pendulum_tf_disc6,7,9,1,-1,'TDFII');
verifyMinimumPhase(pendulum_tf_disc7,9,7,1,-1,'DFI');
verifyMinimumPhase(pendulum_tf_disc8,11,5,1,-1,'DFII');

verifyMinimumPhase(invpendulum_cartpos_tf_disc1,12,4,1,-1,'DFI');
verifyMinimumPhase(invpendulum_cartpos_tf_disc2,2,14,1,-1,'DFII');
verifyMinimumPhase(invpendulum_cartpos_tf_disc3,10,6,1,-1,'TDFII');
verifyMinimumPhase(invpendulum_cartpos_tf_disc4,8,8,1,-1,'DFI');
verifyMinimumPhase(invpendulum_cartpos_tf_disc5,6,10,1,-1,'DFII');
verifyMinimumPhase(invpendulum_cartpos_tf_disc6,7,9,1,-1,'TDFII');
verifyMinimumPhase(invpendulum_cartpos_tf_disc7,9,7,1,-1,'DFI');
verifyMinimumPhase(invpendulum_cartpos_tf_disc8,11,5,1,-1,'DFII');

verifyMinimumPhase(magsuspension_tf_disc1,12,4,1,-1,'DFI');
verifyMinimumPhase(magsuspension_tf_disc2,2,14,1,-1,'DFII');
verifyMinimumPhase(magsuspension_tf_disc3,10,6,1,-1,'TDFII');
verifyMinimumPhase(magsuspension_tf_disc4,8,8,1,-1,'DFI');
verifyMinimumPhase(magsuspension_tf_disc5,6,10,1,-1,'DFII');
verifyMinimumPhase(magsuspension_tf_disc6,7,9,1,-1,'TDFII');
verifyMinimumPhase(magsuspension_tf_disc7,9,7,1,-1,'DFI');
verifyMinimumPhase(magsuspension_tf_disc8,11,5,1,-1,'DFII');

verifyMinimumPhase(cruise_tf_disc1,12,4,1,-1,'DFI');
verifyMinimumPhase(cruise_tf_disc2,2,14,1,-1,'DFII');
verifyMinimumPhase(cruise_tf_disc3,10,6,1,-1,'TDFII');
verifyMinimumPhase(cruise_tf_disc4,8,8,1,-1,'DFI');
verifyMinimumPhase(cruise_tf_disc5,6,10,1,-1,'DFII');
verifyMinimumPhase(cruise_tf_disc6,7,9,1,-1,'TDFII');
verifyMinimumPhase(cruise_tf_disc7,9,7,1,-1,'DFI');

verifyMinimumPhase(tapedriver_tf_disc1,12,4,1,-1,'DFI');
verifyMinimumPhase(tapedriver_tf_disc2,2,14,1,-1,'DFII');
verifyMinimumPhase(tapedriver_tf_disc3,10,6,1,-1,'TDFII');
verifyMinimumPhase(tapedriver_tf_disc4,8,8,1,-1,'DFI');
verifyMinimumPhase(tapedriver_tf_disc5,6,10,1,-1,'DFII');
verifyMinimumPhase(tapedriver_tf_disc6,7,9,1,-1,'TDFII');
verifyMinimumPhase(tapedriver_tf_disc7,9,7,1,-1,'DFI');
verifyMinimumPhase(tapedriver_tf_disc8,11,5,1,-1,'DFII');

verifyMinimumPhase(helicopter_tf_disc1,12,4,1,-1,'DFI');
verifyMinimumPhase(helicopter_tf_disc2,2,14,1,-1,'DFII');
verifyMinimumPhase(helicopter_tf_disc3,10,6,1,-1,'TDFII');
verifyMinimumPhase(helicopter_tf_disc4,8,8,1,-1,'DFI');
verifyMinimumPhase(helicopter_tf_disc5,6,10,1,-1,'DFII');
verifyMinimumPhase(helicopter_tf_disc6,7,9,1,-1,'TDFII');
verifyMinimumPhase(helicopter_tf_disc7,9,7,1,-1,'DFI');
verifyMinimumPhase(helicopter_tf_disc8,11,5,1,-1,'DFII');

verifyMinimumPhase(uscgtampa_tf_disc1,12,4,1,-1,'DFI');
verifyMinimumPhase(uscgtampa_tf_disc2,2,14,1,-1,'DFII');
verifyMinimumPhase(uscgtampa_tf_disc3,10,6,1,-1,'TDFII');
verifyMinimumPhase(uscgtampa_tf_disc4,8,8,1,-1,'DFI');
verifyMinimumPhase(uscgtampa_tf_disc5,6,10,1,-1,'DFII');
verifyMinimumPhase(uscgtampa_tf_disc6,7,9,1,-1,'TDFII');
verifyMinimumPhase(uscgtampa_tf_disc7,9,7,1,-1,'DFI');
verifyMinimumPhase(uscgtampa_tf_disc8,11,5,1,-1,'DFII');

verifyMinimumPhase(magneticpointer_tf_disc1,12,4,1,-1,'DFI');
verifyMinimumPhase(magneticpointer_tf_disc2,2,14,1,-1,'DFII');
verifyMinimumPhase(magneticpointer_tf_disc3,10,6,1,-1,'TDFII');
verifyMinimumPhase(magneticpointer_tf_disc4,8,8,1,-1,'DFI');
verifyMinimumPhase(magneticpointer_tf_disc5,6,10,1,-1,'DFII');
verifyMinimumPhase(magneticpointer_tf_disc6,7,9,1,-1,'TDFII');
verifyMinimumPhase(magneticpointer_tf_disc7,9,7,1,-1,'DFI');
verifyMinimumPhase(magneticpointer_tf_disc8,11,5,1,-1,'DFII');
