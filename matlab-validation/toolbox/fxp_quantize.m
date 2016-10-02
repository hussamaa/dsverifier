function num_quantized = fxp_quantize (num, wl)
% 
% [fxp_quantitized]=fxp_quantize(num , wl)
%
% Fixed point quantization function.
% 'num' is a input value to be quantized
% wl is fractional word lenght
% return the parameter 'num' quantized according to word length and
% implementation values.
%
% Lennon Chaves
% September 29, 2016
% Manaus

a = double(num);
l = double(wl);

num_quantized =(2^(-1*l))*floor(a*(2^l));

end