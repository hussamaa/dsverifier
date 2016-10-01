function [output, time_execution] = dsv_check_limit_cycle(system)
%
% Script developed to simulate automatically all counterexamples 
% by realization form (DFI, DFII and TDFII)
%
% Give the system as a struct with all parameters of counterexample and
% simulate the system.
% 
% Lennon Chaves
% September 20, 2016
% Manaus

    if strcmp(system.impl.realization_form,'DFI') || strcmp(system.impl.realization_form,'DDFI')
        [output, time_execution] = realization_direct_form_1(system);
    elseif strcmp(system.impl.realization_form,'DFII') || strcmp(system.impl.realization_form,'DDFII')
        [output, time_execution]  = realization_direct_form_2(system);
    elseif strcmp(system.impl.realization_form,'TDFII') || strcmp(system.impl.realization_form,'TDDFII')
        [output, time_execution]  = realization_transposed_direct_form_2(system);
    end
end
