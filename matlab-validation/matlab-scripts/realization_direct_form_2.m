function [y] = realization_direct_form_2(system)
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
wl = system.impl.frac_bits;

a_fxp = fxp_quantize(system.sys.a,wl);
b_fxp = fxp_quantize(system.sys.b,wl);

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
    
    y(i) = fxp_quantize(sum, wl);
end

end
