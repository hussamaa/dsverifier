function [fxp_num] = fxp_mult(amult, bmult, impl_int, impl_frac)
% 
% [fxp_num]=fxp_mult(amult,bmult,impl_frac)
% 
% Fixed point multiplication out = amult * bmult
% amult is fixed point input
% bmult is fixed point input
% impl_frac is fractionary implementation
% Return the product result of fixed point inputs amult and bmult
%     
% Lennon Chaves
% September 18, 2016
% Manaus

fxp = fimath(...
  'RoundingMethod','Floor', ...
  'OverflowAction','Wrap');

word_lenght = impl_int + impl_frac;

fxp_amult = fi(amult,1,word_lenght,impl_frac, fxp);
fxp_bmult = fi(bmult,1,word_lenght,impl_frac, fxp);

fxp_num = double(mpy(fxp, fxp_amult, fxp_bmult));

end