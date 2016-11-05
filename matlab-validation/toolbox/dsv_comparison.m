function [output] = dsv_comparison(system, p)
%
% Script to verify and compare the results between MATLAB and DSVerifier
% Give the system as input on this function and check if the outputs of
% MATLAB and DSVerifier are the same.
% 
% Function: [output] = dsv_comparison(system, p)
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
% The parameter 'p' is the property to be analyzed: minimum phase (m), stability (s), overflow(o), limit cycle (lc).
%
% The output is the feedback returned from comparison (successful or failed);
%
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

if (strcmp(p,'lc'))

count = 0;
max_error = 0.1;
for i=1:system.impl.x_size
    fxp_out_ver = abs(system.output.output_verification(i));
    fxp_out_sim = abs(system.output.output_simulation(i));
    erro = abs(fxp_out_ver-fxp_out_sim);
    if erro < max_error
       count = count + 1;
    end
end
    if count == system.impl.x_size
        output = 'Successful';
    else
        output = 'Failed';
    end

elseif (strcmp(p,'o'))
n = system.impl.int_bits;
l = system.impl.frac_bits;

min_wl = -1*((2^(n-1)));
max_wl = ((2^(n-1))-2^(-1*l));
y = system.output.output_simulation;
result = 0;

for i=1:system.impl.x_size

if (y(i) >= max_wl || y(i) <= min_wl)
        result=1;
        break;
end

end

if result == 1
  output = 'Successful';
else
  output = 'Failed';
end

else

 if (strcmp(lower(strtrim(system.output.output_verification)),lower(strtrim(system.output.output_simulation))))
	output = 'Successful';
    else
        output = 'Failed';
 end

end

end
