function verify_overflow(system, bmc, realization, xsize, varargin)
%
% Function: VERIFY_OVERFLOW(system, bmc, realization, xsize)
% Checks overflow property violation for digital systems using a bounded model checking tool.
%
% Where
%   system: represents a struct with digital system represented in transfer-function;
%   bmc: set the BMC back-end for DSVerifier (ESBMC or CBMC);
%   realization: set the realization for the Digital-System (DFI, DFII, TDFII, DDFI, DDFII, and TDDFII);
%   xsize:  set the bound of verification.
%
%  The 'system' must be structed as follow:
%  system.system = tf(den,num,ts): transfer function representation (den - denominator, num - numerator, ts - sample time);
%  or system.system = c2d(sys,ts): if the digital system should be discretized
%  
%  See also TF and C2D.
%
%  system.impl.int_bits: integer bits implementation;
%  system.impl.frac_bits: fractional bits representation;
%  system.range.max = max dynamical range;
%  system.range.min = min dynamical range;
%  system.delta = delta operator (it must be '0' if it is not a delta realization).
%
% Another usage form is adding other parameters (optional parameters) as follow:
%
% VERIFY_OVERFLOW(system, bmc, realization, xsize, solver, ovmode, rmode, emode, timeout)
%
% Where
%  solver: use the specified solver in BMC back-end which could be 'Z3', 'boolector', 'yices', 'cvc4', 'minisat';
%  ovmode: set the overflow mode which could be 'WRAPAROUND' or 'SATURATE';
%  rmode: set the rounding mode which could be 'ROUNDING', 'FLOOR', or 'CEIL';
%  emode: set the error mode which could be 'ABSOLUTE' or 'RELATIVE';
%  timeout: configure time limit, integer followed by {s,m,h} (for ESBMC only).
%
% Example of usage:
%  num = [...];
%  den = [...];
%  ds.system = tf(den,num,ts);
%  ds.impl.int_bits = ...;
%  ds.impl.frac_bits = ...;
%  ds.range.max = ...;
%  ds.range.min = -...;
%  ds.delta = ...;
%
%  VERIFY_OVERFLOW(ds,'CBMC','DFI',10);
%  VERIFICATION SUCCESSFUL!
%
% Author: Lennon Chaves
% Federal University of Amazonas
% October, 2016
%
global property;
%setting the DSVERIFIER_HOME
dsv_setup();
%translate to ANSI-C file
dsv_parser(system,'tf',0);
%verifying using DSVerifier command-line
property = 'OVERFLOW';

extra_param = get_macro_params(nargin,varargin,'tf');

command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc extra_param];
dsv_verification(command_line,'tf');
%report the verification
output = dsv_report('output.out','tf');
disp(output);

end

