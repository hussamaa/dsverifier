function verify_cl_quantization_error(system, bmc, realization, xsize, c_mode, error, varargin)
%
% Function: VERIFY_CL_QUANTIZATION_ERROR(system, bmc, realization, xsize, c_mode, error)
% Checks quantization error property violation for closed-loop digital systems using a bounded model checking tool.
%
% Where
%   system: represents a struct with digital system represented in transfer-function;
%   bmc: set the BMC back-end for DSVerifier (ESBMC or CBMC);
%   realization: set the realization for the Digital-System (DFI, DFII, TDFII, DDFI, DDFII, and TDDFII);
%   xsize:  set the bound of verification;
%   c_mode: set the connection mode for the closed-loop system (SERIES or FEEDBACK);
%   error: set the error limit.
%
%  The 'system' must be structed as follow:
%  system.system.controller = TF(den,num,ts): controller for closed-loop digital system (or use C2D for digital systems that must be discretized) ;
%  system.system.plant = TF(den,num,ts): plant for closed-loop digital system (or use C2D for digital systems that must be discretized);
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
% VERIFY_CL_QUANTIZATION_ERROR(system, bmc, realization, xsize, error, solver, ovmode, rmode, emode, timeout)
%
% Where
%  solver: use the specified solver in BMC back-end which could be 'Z3', 'boolector', 'yices', 'cvc4', 'minisat';
%  ovmode: set the overflow mode which could be 'WRAPAROUND' or 'SATURATE';
%  rmode: set the rounding mode which could be 'ROUNDING', 'FLOOR', or 'CEIL';
%  emode: set the error mode which could be 'ABSOLUTE' or 'RELATIVE';
%  timeout: configure time limit, integer followed by {s,m,h} (for ESBMC only).
%
% Example of usage:
%  numplant = [...];
%  denplant = [...];
%  ds.system.plant = tf(denplant,numplant,ts);
%  numcontrol = [...];
%  dencontrol = [...];
%  ds.system.controller = tf(dencontrol,numcontrol,ts);
%  ds.impl.int_bits = ...;
%  ds.impl.frac_bits = ...;
%  ds.range.max = ...;
%  ds.range.min = -...;
%  ds.delta = ...;
%
%  VERIFY_CL_QUANTIZATION_ERROR(ds,'CBMC','DFI',10, 0.18);
%  VERICATION FAILED!
%
% Author: Lennon Chaves
% Federal University of Amazonas
% October, 2016
%
global property;

%setting the DSVERIFIER_HOME
dsv_setup();

%translate to ANSI-C file
dsv_parser(system,'cl', error);

%verifying using DSVerifier command-line
property = 'QUANTIZATION_ERROR_CLOSED_LOOP';

extra_param = get_macro_params(nargin-1,varargin,'cl');

command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc  ' --connection-mode ' c_mode extra_param];
dsv_verification(command_line,'cl');

%report the verification
output = dsv_report('output.out','cl');
disp(output);

end

