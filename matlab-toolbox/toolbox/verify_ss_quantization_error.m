function verify_ss_quantization_error(system, bmc, realization, xsize, error, varargin)
%
% Checks quantization error property violation for digital systems (state-space representation) using a bounded model checking tool.
% Function: VERIFY_SS_QUANTIZATION_ERROR(system, bmc, realization, xsize, error)
%
% Where
%   system: represents a struct with digital system represented in state-space;
%   bmc: set the BMC back-end for DSVerifier (ESBMC or CBMC);
%   realization: set the realization for the Digital-System (DFI, DFII, TDFII, DDFI, DDFII, and TDDFII);
%   xsize:  set the bound of verification.
%   error: set the error limits
%
%  The 'system' must be structed as follow:
%  system.system = ss(A,B,C,D,ts): state-space representation (A, B, C and D represent the matrix for state-space system, ts - sample time);
%  or system.system = c2d(sys,ts): if the state-space representation should be discretized.
%  
%  See also SS and C2D.
%
%  system.inputs: the vector of inputs that will be interacted during the verification;
%  system.impl.int_bits: integer bits implementation;
%  system.impl.frac_bits: fractional bits representation;
%
% Another usage form is adding other parameters (optional parameters) as follow:
%
% VERIFY_SS_QUANTIZATION_ERROR(system, bmc, realization, xsize, error, solver, ovmode, rmode, emode, timeout)
%
% Where
%  solver: use the specified solver in BMC back-end which could be 'Z3', 'boolector', 'yices', 'cvc4', 'minisat';
%  ovmode: set the overflow mode which could be 'WRAPAROUND' or 'SATURATE';
%  rmode: set the rounding mode which could be 'ROUNDING', 'FLOOR', or 'CEIL';
%  emode: set the error mode which could be 'ABSOLUTE' or 'RELATIVE';
%  timeout: configure time limit, integer followed by {s,m,h} (for ESBMC only).
%
% Example of usage:
%  A = [...];
%  B = [...];
%  C = [...];
%  D = [...];
%  sys = ss(A,B,C,D);
%  ds.system = c2d(sys,ts);
%  ds.inputs = [...];
%  ds.impl.int_bits = ...;
%  ds.impl.frac_bits = ...;
%
%  VERIFY_SS_QUANTIZATION_ERROR(ds,'CBMC','DFI',10,0.18);
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
dsv_parser(system,'ss',error);
%verifying using DSVerifier command-line
property = 'QUANTISATION_ERROR';

extra_param = get_macro_params(nargin-1,varargin,'ss');

command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc extra_param];
dsv_verification(command_line,'ss');
%report the verification
output = dsv_report('output.out','ss');
disp(output);
end

