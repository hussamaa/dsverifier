function [y, time_execution] = realization_direct_form_1(system)
% 
% [y]= realization_direct_form_1(system)
% 
% System is a transfer function system including not only numerator or
% denominator, but implementation about the system.
% system is the input of DFI realization and should be implemented as a
% struct in MATLAB Worksapace as:
% system.sys.a = denominator of transfer function
% system.sys.b = numerator of transfer function
% system.impl.int_bits = integer bits
% system.impl.frac_bits = fractionary bits
% system.inputs.const_inputs with the inputs to realization
% system.inputs.initial_states with the initial states
% system.impl.x_size with the bound of the realization
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

x_aux = system.inputs.const_inputs(1:Nb);
y_aux = system.inputs.initial_states;

x =  system.inputs.const_inputs;
y =  zeros(1,x_size);

%% DFI Realization
for i=1:x_size
    sum = 0;
	a_ptr = a_fxp;
    b_ptr = b_fxp;
    
    x_aux = shiftL(x(i), x_aux, Nb);
	y_ptr = fliplr(y_aux);
	x_ptr = fliplr(x_aux);
    
    for j=1:Nb
		sum = fxp_add(sum, fxp_mult(b_ptr(j), x_ptr(j), wl), wl);
    end
    
    for k=2:Na
		sum = fxp_sub(sum, fxp_mult(a_ptr(k), y_ptr(k-1),wl),wl);
    end
    
    sum = fxp_div(sum,a_fxp(1),wl);
    
    if (strcmp(overflow_mode,'wrap'))
    y(i) = mode_wrap(sum, wl+ system.impl.int_bits-1);
    elseif (strcmp(overflow_mode,'saturate'))
    y(i) = mode_saturate(sum, wl+ system.impl.int_bits-1);
    end
    
    y_aux = shiftL(y(i), y_aux, Na);

end
time_execution = toc;
end