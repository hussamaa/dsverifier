function fxp_num = fxp_add(aadd, badd, wl)
% 
% Function to perform a fixed point addition out = a + b;
%
% Function: [fxp_num] = fxp_add(aadd,badd,wl)
% 
% Where:
% aadd is fixed point input
% badd is fixed point input
% wl is fractional word lenght
%
% return result of summing the inputs
%     
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

fxp_aadd= fxp_rounding(aadd,wl);
fxp_badd= fxp_rounding(badd,wl);

fxp_num = fxp_rounding(fxp_aadd + fxp_badd, wl);

end
