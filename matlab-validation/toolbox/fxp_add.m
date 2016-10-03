function fxp_num = fxp_add(aadd, badd, wl)
% 
% [fxp_num]=fxp_add(aadd,badd,wl)
% 
% Fixed point addition out = a + b
% aadd is fixed point input
% badd is fixed point input
% wl is fractional word lenght
% return result of summing the inputs
%     
% Lennon Chaves
% September 29, 2016
% Manaus

fxp_aadd= fxp_quantize(aadd,wl);
fxp_badd= fxp_quantize(badd,wl);

fxp_num = fxp_quantize(fxp_aadd + fxp_badd, wl);

end