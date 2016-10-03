function fxp_num = fxp_mult(amult, bmult, wl)
% 
% [fxp_num]=fxp_mult(amult,bmult,wl)
% 
% Fixed point multiplication out = amult * bmult
% amult is fixed point input
% bmult is fixed point input
% wl is fractional word lenght
% Return the product result of fixed point inputs amult and bmult
%     
% Lennon Chaves
% September 29, 2016
% Manaus

fxp_amult= fxp_quantize(amult,wl);
fxp_bmult= fxp_quantize(bmult,wl);

fxp_num = fxp_quantize(fxp_amult*fxp_bmult, wl);

end