function [output] = dsv_simulation(system)
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

    if strcmp(system.impl.realization_form,'DFI')
        output = realization_direct_form_1(system);
    elseif strcmp(system.impl.realization_form,'DFII')
        output = realization_direct_form_2(system);
    elseif strcmp(system.impl.realization_form,'TDFII')
        output = realization_transposed_direct_form_2(system);
    end
end
