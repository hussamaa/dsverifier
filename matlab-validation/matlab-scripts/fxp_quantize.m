function [fxp_quantitized] = fxp_quantize (a, impl_int, impl_frac)
% 
% [fxp_quantitized]=fxp_quantize(a, impl_bits, impl_frac)
%
% Fixed point quantization function.
% 'a' is a input value to be quantized
% 'impl_int' is integer implementation bits
% 'impl_frac' is fractionary implementation bits
% return the parameter 'a' quantized according to word length and
% implementation values.
%
% Lennon Chaves
% September 18, 2016
% Manaus

%Overflow: Saturate/Wrap
%Rounding Mode: Floor, Nearest, Round, Ceiling, Zero
fxp = fimath(...
  'RoundingMethod','Floor', ...
  'OverflowAction','Wrap');

word_lenght = impl_int + impl_frac;

fxp_quantitized = double(fi(a,1,word_lenght,impl_frac, fxp));

end