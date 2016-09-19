function [fxp_num] = fxp_add(aadd, badd, impl_int, impl_frac)
% 
% [fxp_num]=fxp_add(aadd,badd)
% 
% Fixed point addition out = a + b
% aadd is fixed point input
% badd is fixed point input
% return result of summing the inputs
%     
% Lennon Chaves
% September 18, 2016
% Manaus

fxp = fimath(...
  'RoundingMethod','Floor', ...
  'OverflowAction','Wrap');

word_lenght = impl_int + impl_frac;

fxp_aadd= fi(aadd,1,word_lenght,impl_frac, fxp);
fxp_badd = fi(badd,1,word_lenght,impl_frac, fxp);

fxp_num = double(fxp_aadd + fxp_badd);

end