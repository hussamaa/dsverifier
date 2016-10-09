function fxp_num = fxp_mult(amult, bmult, wl)
% 
% Function to perform a fixed point multiplication out = amult * bmult
%
% Function: [fxp_num]=fxp_mult(amult,bmult,wl)
% 
% where:
% amult is fixed point input
% bmult is fixed point input
% wl is fractional word lenght
%
% Return the product result of fixed point inputs amult and bmult
%     
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

fxp_amult= fxp_quantize(amult,wl);
fxp_bmult= fxp_quantize(bmult,wl);

fxp_num = fxp_quantize(fxp_amult*fxp_bmult, wl);

end
