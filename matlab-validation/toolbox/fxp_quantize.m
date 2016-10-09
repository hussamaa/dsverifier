function num_quantized = fxp_quantize (num, wl)
% 
% Function to perform a fixed point quantization function.
%
% Function: [fxp_quantitized]=fxp_quantize(num , wl)
% 
% where:
% num is a input value to be quantized
% wl is fractional word lenght
%
% return the parameter 'num' quantized according to word length and
% implementation values.
%
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

global round_mode;

a = double(num);
l = double(wl);

if (strcmp(round_mode,'round'))
num_quantized =(2^(-1*l))*round(a*(2^l));
elseif (strcmp(round_mode,'floor'))
num_quantized =(2^(-1*l))*floor(a*(2^l));
end

end
