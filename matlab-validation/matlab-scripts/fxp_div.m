function [fxp_num] = fxp_div(adiv,bdiv, impl_int, impl_frac)
% 
% [fxp_num]=fxp_div(adiv,bdiv,impl_frac)
% Fixed point division out = a / b
% adiv is fixed point input
% bdiv is fixed point input
% impl_frac is fractionary implementation
% return div result out
%
% Lennon Chaves
% September 18, 2016
% Manaus

word_lenght = impl_int + impl_frac;

fxp = fimath(...
  'RoundingMethod','Floor', ...
  'OverflowAction','Wrap');

T = numerictype('Signed',true,'WordLength',word_lenght,...
					      'FractionLength',impl_frac);

fxp_adiv = fi(adiv,1,word_lenght,impl_frac, fxp);
fxp_bdiv = fi(bdiv,1,word_lenght,impl_frac, fxp);

fxp_num = double(divide(T,fxp_adiv,fxp_bdiv));

end
