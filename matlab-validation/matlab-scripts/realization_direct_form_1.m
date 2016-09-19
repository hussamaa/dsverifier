function [y] = realization_direct_form_1(system)
% 
% [y]= realization_direct_form_1(system)
% 
% System is a transfer function system including not only numerator or
% denominator, but implementation about the system.
% system is the input of DFI realization and should be implemented as a
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
a_fxp = system.a;
b_fxp = system.b;

impl_int = system.impl.int_bits;
impl_frac = system.impl.frac_bits;

x_size = system.x_size;

Na = length(a_fxp);
Nb = length(b_fxp);

x_aux = system.inputs(1:Nb);
y_aux = system.initial_states;

x =  system.inputs;
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
		sum = fxp_add(sum, fxp_mult(b_ptr(j), x_ptr(j), impl_int, impl_frac),impl_int, impl_frac);
    end
    
    for k=2:Na;
		sum = fxp_sub(sum, fxp_mult(a_ptr(k), y_ptr(k-1),impl_int, impl_frac),impl_int, impl_frac);
    end
    
    sum = fxp_div(sum,a_fxp(1),impl_int, impl_frac);
    
    y(i) = fxp_quantize(sum, impl_int, impl_frac);
    
    y_aux = shiftL(y(i), y_aux, Na);
end