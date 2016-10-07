function [y, time_execution] = dsv_df2(system)
% 
% [y]= realization_direct_form_2(system)
% 
% System is a transfer function system including not only numerator or
% denominator, but implementation about the system.
% system is the input of DFII realization and should be implemented as a
% struct in MATLAB Worksapace as:
% system.a = denominator of transfer function
% system.b = numerator of transfer function
% system.impl.int_bits = integer bits
% system.impl.frac_bits = fractionary bits
% system.inputs with the inputs to realization
% system.initial_states with the initial states
% system.x_size with the bound of the realization
%
% Lennon Chaves
% September 18, 2016
% Manaus

%% Definitions

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
    w_aux = shiftR(0, w_aux, Nw);
    
    sum = 0;
	a_ptr = a_fxp;
	b_ptr = b_fxp;
	w_ptr = w_aux;
    
    for k=2:Na
		w_aux(1) = fxp_sub(w_aux(1), fxp_mult(a_ptr(k), w_ptr(k), wl),wl);
    end
     
    w_aux(1) = fxp_add(w_aux(1), x(i), wl);
    w_aux(1) = fxp_div(w_aux(1), a_fxp(1), wl);
  
	w_ptr = w_aux;
   
    for j=1:Nb
		sum = fxp_add(sum, fxp_mult(b_ptr(j), w_ptr(j), wl), wl);
    end
    
    if (strcmp(overflow_mode,'wrap'))
    y(i) = mode_wrap(sum, wl+ system.impl.int_bits-1);
    elseif (strcmp(overflow_mode,'saturate'))
    y(i) = mode_saturate(sum, wl+ system.impl.int_bits-1);
    end
end

time_execution = toc;
end
