function [fxp_num] = fxp_sub(asub, bsub,impl_int, impl_frac)
% 
% [fxp_num]=fxp_add(aadd,badd)
% 
% Fixed point subtraction out = a - b
% asub is fixed point input
% bsub is fixed point input
% return result of subtracting the inputs
%     
% Lennon Chaves
% September 18, 2016
% Manaus

fxp = fimath(...
  'RoundingMethod','Floor', ...
  'OverflowAction','Wrap');

word_lenght = impl_int + impl_frac;

fxp_asub = fi(asub,1,word_lenght,impl_frac, fxp);
fxp_bsub = fi(bsub,1,word_lenght,impl_frac, fxp);

fxp_num = double(fxp_asub - fxp_bsub);

end
