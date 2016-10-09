function fxp_num = fxp_div(adiv,bdiv, wl)
% 
% Function to perform a fixed point division out = a / b
%
% Function: [fxp_num]=fxp_div(adiv,bdiv,wl)
% 
% where:
% adiv is fixed point input
% bdiv is fixed point input
% wl is fractional word lenght
%
% return div result out
%
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

fxp_adiv= fxp_quantize(adiv,wl);
fxp_bdiv= fxp_quantize(bdiv,wl);

fxp_num = fxp_quantize(fxp_adiv/fxp_bdiv, wl);

end
