function [y, time_execution] = dsv_tdf2(system)
% 
% Simulate and reproduce a counterexample for limit cycle using DDFII realization.
% In case of delta form (TDDFI), the delta operator should be represented in system struct.
%
% Function: [y, time_execution] = dsv_tdf2(system)
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
% The parameter 'y' is the output returned from simulation;
% The time execution is the time to execute the simulation;
%
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

tic

global overflow_mode;

wl = system.impl.frac_bits;

if (system.impl.delta > 0)
[a_num, b_num] = deltapoly(system.sys.b, system.sys.a, system.impl.delta);
else
a_num = system.sys.a;
b_num = system.sys.b;
end

a_fxp = fxp_quantize(a_num,wl);
b_fxp = fxp_quantize(b_num,wl);

x_size = system.impl.x_size;

Na = length(a_fxp);
Nb = length(b_fxp);

if (Na > Nb)
    Nw = Na;
else
    Nw = Nb;
end

w_aux = system.inputs.initial_states;

x =  system.inputs.const_inputs;
y =  zeros(1,x_size);

%% DFII Realization
for i=1:x_size
    
    yout = 0;
	a_ptr = a_fxp;
	b_ptr = b_fxp;
    w = w_aux;
  
	yout = fxp_add(fxp_mult(b_ptr(1), x(i), wl), w(1), wl);
	yout = fxp_div(yout, a_fxp(1), wl);
    
    for j=1:(Nw-1)
		w(j) = w(j+1);
        if (j < Na)
			w(j) = fxp_sub(w(j), fxp_mult(a_ptr(j+1), yout, wl), wl);
        end
        
        if (j < Nb)
			w(j) = fxp_add(w(j), fxp_mult(b_ptr(j+1), x(i), wl), wl);
        end
    end
    
    if (strcmp(overflow_mode,'wrap'))
    y(i) = mode_wrap(yout, system.impl.int_bits, system.impl.frac_bits);
    elseif (strcmp(overflow_mode,'saturate'))
    y(i) = mode_saturate(yout, system.impl.int_bits, system.impl.frac_bits);
    else
    y(i) = yout;
    end
    w_aux = w;
    
end

time_execution = toc;
end
