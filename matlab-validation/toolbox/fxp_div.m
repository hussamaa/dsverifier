function fxp_num = fxp_div(adiv,bdiv, wl)
% 
% [fxp_num]=fxp_div(adiv,bdiv,wl)
% Fixed point division out = a / b
% adiv is fixed point input
% bdiv is fixed point input
% wl is fractional word lenght
% return div result out
%
% Lennon Chaves
% September 29, 2016
% Manaus

fxp_adiv= fxp_quantize(adiv,wl);
fxp_bdiv= fxp_quantize(bdiv,wl);

fxp_num = fxp_quantize(fxp_adiv/fxp_bdiv, wl);

end
