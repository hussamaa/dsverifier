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

verifyOverflow(dcmotor_tf_disc1,12,4,1,-1,'DFI', 10);
verifyOverflow(dcmotor_tf_disc2,2,14,1,-1,'DFII', 10);
verifyOverflow(dcmotor_tf_disc3,10,6,1,-1,'TDFII', 10);
verifyOverflow(dcmotor_tf_disc4,8,8,1,-1,'DFI', 10);
verifyOverflow(dcmotor_tf_disc5,6,10,1,-1,'DFII', 10);
verifyOverflow(dcmotor_tf_disc6,7,9,1,-1,'TDFII', 10);
verifyOverflow(dcmotor_tf_disc7,9,7,1,-1,'DFI', 10);
verifyOverflow(dcmotor_tf_disc8,11,5,1,-1,'DFII', 10);

verifyOverflow(pendulum_tf_disc1,12,4,1,-1,'DFI', 10);
verifyOverflow(pendulum_tf_disc2,2,14,1,-1,'DFII', 10);
verifyOverflow(pendulum_tf_disc3,10,6,1,-1,'TDFII', 10);
verifyOverflow(pendulum_tf_disc4,8,8,1,-1,'DFI', 10);
verifyOverflow(pendulum_tf_disc5,6,10,1,-1,'DFII', 10);
verifyOverflow(pendulum_tf_disc6,7,9,1,-1,'TDFII', 10);
verifyOverflow(pendulum_tf_disc7,9,7,1,-1,'DFI', 10);
verifyOverflow(pendulum_tf_disc8,11,5,1,-1,'DFII', 10);

verifyOverflow(invpendulum_cartpos_tf_disc1,12,4,1,-1,'DFI', 10);
verifyOverflow(invpendulum_cartpos_tf_disc2,2,14,1,-1,'DFII', 10);
verifyOverflow(invpendulum_cartpos_tf_disc3,10,6,1,-1,'TDFII', 10);
verifyOverflow(invpendulum_cartpos_tf_disc4,8,8,1,-1,'DFI', 10);
verifyOverflow(invpendulum_cartpos_tf_disc5,6,10,1,-1,'DFII', 10);
verifyOverflow(invpendulum_cartpos_tf_disc6,7,9,1,-1,'TDFII', 10);
verifyOverflow(invpendulum_cartpos_tf_disc7,9,7,1,-1,'DFI', 10);
verifyOverflow(invpendulum_cartpos_tf_disc8,11,5,1,-1,'DFII', 10);

verifyOverflow(magsuspension_tf_disc1,12,4,1,-1,'DFI', 10);
verifyOverflow(magsuspension_tf_disc2,2,14,1,-1,'DFII', 10);
verifyOverflow(magsuspension_tf_disc3,10,6,1,-1,'TDFII', 10);
verifyOverflow(magsuspension_tf_disc4,8,8,1,-1,'DFI', 10);
verifyOverflow(magsuspension_tf_disc5,6,10,1,-1,'DFII', 10);
verifyOverflow(magsuspension_tf_disc6,7,9,1,-1,'TDFII', 10);
verifyOverflow(magsuspension_tf_disc7,9,7,1,-1,'DFI', 10);
verifyOverflow(magsuspension_tf_disc8,11,5,1,-1,'DFII', 10);

verifyOverflow(cruise_tf_disc1,12,4,1,-1,'DFI', 10);
verifyOverflow(cruise_tf_disc2,2,14,1,-1,'DFII', 10);
verifyOverflow(cruise_tf_disc3,10,6,1,-1,'TDFII', 10);
verifyOverflow(cruise_tf_disc4,8,8,1,-1,'DFI', 10);
verifyOverflow(cruise_tf_disc5,6,10,1,-1,'DFII', 10);
verifyOverflow(cruise_tf_disc6,7,9,1,-1,'TDFII', 10);
verifyOverflow(cruise_tf_disc7,9,7,1,-1,'DFI', 10);

verifyOverflow(tapedriver_tf_disc1,12,4,1,-1,'DFI', 10);
verifyOverflow(tapedriver_tf_disc2,2,14,1,-1,'DFII', 10);
verifyOverflow(tapedriver_tf_disc3,10,6,1,-1,'TDFII', 10);
verifyOverflow(tapedriver_tf_disc4,8,8,1,-1,'DFI', 10);
verifyOverflow(tapedriver_tf_disc5,6,10,1,-1,'DFII', 10);
verifyOverflow(tapedriver_tf_disc6,7,9,1,-1,'TDFII', 10);
verifyOverflow(tapedriver_tf_disc7,9,7,1,-1,'DFI', 10);
verifyOverflow(tapedriver_tf_disc8,11,5,1,-1,'DFII', 10);

verifyOverflow(helicopter_tf_disc1,12,4,1,-1,'DFI', 10);
verifyOverflow(helicopter_tf_disc2,2,14,1,-1,'DFII', 10);
verifyOverflow(helicopter_tf_disc3,10,6,1,-1,'TDFII', 10);
verifyOverflow(helicopter_tf_disc4,8,8,1,-1,'DFI', 10);
verifyOverflow(helicopter_tf_disc5,6,10,1,-1,'DFII', 10);
verifyOverflow(helicopter_tf_disc6,7,9,1,-1,'TDFII', 10);
verifyOverflow(helicopter_tf_disc7,9,7,1,-1,'DFI', 10);
verifyOverflow(helicopter_tf_disc8,11,5,1,-1,'DFII', 10);

verifyOverflow(uscgtampa_tf_disc1,12,4,1,-1,'DFI', 10);
verifyOverflow(uscgtampa_tf_disc2,2,14,1,-1,'DFII', 10);
verifyOverflow(uscgtampa_tf_disc3,10,6,1,-1,'TDFII', 10);
verifyOverflow(uscgtampa_tf_disc4,8,8,1,-1,'DFI', 10);
verifyOverflow(uscgtampa_tf_disc5,6,10,1,-1,'DFII', 10);
verifyOverflow(uscgtampa_tf_disc6,7,9,1,-1,'TDFII', 10);
verifyOverflow(uscgtampa_tf_disc7,9,7,1,-1,'DFI', 10);
verifyOverflow(uscgtampa_tf_disc8,11,5,1,-1,'DFII', 10);

verifyOverflow(magneticpointer_tf_disc1,12,4,1,-1,'DFI', 10);
verifyOverflow(magneticpointer_tf_disc2,2,14,1,-1,'DFII', 10);
verifyOverflow(magneticpointer_tf_disc3,10,6,1,-1,'TDFII', 10);
verifyOverflow(magneticpointer_tf_disc4,8,8,1,-1,'DFI', 10);
verifyOverflow(magneticpointer_tf_disc5,6,10,1,-1,'DFII', 10);
verifyOverflow(magneticpointer_tf_disc6,7,9,1,-1,'TDFII', 10);
verifyOverflow(magneticpointer_tf_disc7,9,7,1,-1,'DFI', 10);
verifyOverflow(magneticpointer_tf_disc8,11,5,1,-1,'DFII', 10);
