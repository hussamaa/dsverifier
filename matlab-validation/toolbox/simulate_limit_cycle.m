function [output, time_execution] = simulate_limit_cycle(system)
%
% Script developed to simulate the limit cycle counterexamples using DFI, DFII and TDFII realizations.
%
% Give the system as a struct with all parameters of counterexample and
% simulate the system.
% 
% Function: [output, time_execution] = simulate_limit_cycle(system)
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
%
% The output is the feedback returned from simulation;
% The time execution is the time to execute the simulation;
%
% Lennon Chaves
% November 04, 2016
% Manaus, Brazil

    if strcmp(system.impl.realization_form,'DFI') || strcmp(system.impl.realization_form,'DDFI')
        [output, time_execution] = dsv_df1(system);
    elseif strcmp(system.impl.realization_form,'DFII') || strcmp(system.impl.realization_form,'DDFII')
        [output, time_execution]  = dsv_df2(system);
    elseif strcmp(system.impl.realization_form,'TDFII') || strcmp(system.impl.realization_form,'TDDFII')
        [output, time_execution]  = dsv_tdf2(system);
    end
end
