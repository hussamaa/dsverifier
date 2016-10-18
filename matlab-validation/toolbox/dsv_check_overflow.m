function [output, time_execution] = dsv_check_overflow(system)
%
% Script developed to reproduce the overflow property in counterexamples
%
% Give the system as a struct with all parameters of counterexample and matlab will check overflow property for direct and delta forms.
% 
% Function: [output, time_execution] = dsv_check_overflow(system)
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
% October 09, 2016
% Manaus

tic

a = system.sys.a;
b = system.sys.b;
u = system.inputs.const_inputs;
delta = system.impl.delta;
l = system.impl.frac_bits;
n = system.impl.int_bits - 1;

if delta > 0
    [at,bt]=deltapoly(b,a,delta);
else
    at=a;
    bt=b;
end
for i=1:length(at)
at(i) = mode_saturate(at(i),n+1,l);
end
for i=1:length(bt)
bt(i) = mode_saturate(bt(i),n+1,l);
end

uf=u;

y=dlsim(bt,at,uf);
min = -1*((2^n));
max = ((2^n)-2^(-1*l));

for i=1:length(y)
    if (y(i)> max) || (y(i)< min)
        result=1;
        %'An overflow occurred'
        break;
    else
 	%'There were no overflow');
        result=0;
    end
end

if result == 1
    output = 'Failed';
else
    output = 'Successfull';
end

time_execution = toc;
end
