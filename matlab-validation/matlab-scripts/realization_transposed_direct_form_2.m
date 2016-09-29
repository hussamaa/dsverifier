function [y] = realization_transposed_direct_form_2(system)
% 
% [y]= realization_transposed_direct_form_2(system)
% 
% System is a transfer function system including not only numerator or
% denominator, but implementation about the system.
% system is the input of TDFII realization and should be implemented as a
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

if (system.impl.delta > 0)
[a_num, b_den] = deltapoly(system.sys.b, system.sys.a, system.impl.delta);
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
    
    y(i) = fxp_quantize(yout, wl);
    w_aux = w;
    
end

end
