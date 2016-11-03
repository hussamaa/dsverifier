function [output_validation, output_overflow_mode] = dsv_reproduce_limit_cycle(system, ovmode)
%
% Script developed to reproduce the limit cycle counterexamples using DFI,
% DFII and TDFII realizations, that considers the overflow mode effects.
%
% Give the system as a struct with all parameters of counterexample and the automated validation will simulate the system.
% 
% Function: [output_validation, output_overflow_mode] = dsv_check_limit_cycle(system, ovmode)
%
% The struct 'system' should have the following features:
% system.sys.a = denominator;
% system.sys.b = numerator;
% system.sys.tf = transfer function system representation
% system.impl.frac_bits = fractionary bits
% system.impl.int_bits = integer bits
% system.impl.realization_form = realization, and it should be DFI, DFII, TDFII, DDFI, DDFII or TDDFII
% system.inputs.const_inputs = the inputs from counterexample
% system.inputs.initial_states = the initial states from counterexample
% system.outputs.output_verification = the output extracted from counterexample
% system.impl.delta = in delta form realizations, the delta operator should be informed
% system.impl.sample_time = sample time of realization
% system.impl.x_size = the bound size
%
% And ovmode is the overflow mode, and it could be: 'wrap' or 'saturate';
%
% The outputs are the result from simulation considering the overflow mode
% effects.
%
% Lennon Chaves
% November 1, 2016
% Manaus, Brazil

global overflow_mode;
global round_mode;

overflow_mode = ovmode;

if strcmp(overflow_mode,'')
    round_mode = '';
elseif strcmp(overflow_mode,'wrap')
    round_mode = 'round';
else
    round_mode = 'floor';
end

    if strcmp(system.impl.realization_form,'DFI') || strcmp(system.impl.realization_form,'DDFI')
        output_overflow_mode = dsv_df1(system);
    elseif strcmp(system.impl.realization_form,'DFII') || strcmp(system.impl.realization_form,'DDFII')
        output_overflow_mode = dsv_df2(system);
    elseif strcmp(system.impl.realization_form,'TDFII') || strcmp(system.impl.realization_form,'TDDFII')
       output_overflow_mode = dsv_tdf2(system);
    end
    
 output_validation = system.output.output_simulation;
 
 disp('Output from Validation (by default - wrap-around) :');   
 disp(output_validation);
 disp('Output according to Overflow Mode:');
 disp(output_overflow_mode);
end
