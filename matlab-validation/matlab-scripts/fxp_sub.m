function fxp_num = fxp_sub(asub, bsub, wl)
% 
% [fxp_num]=fxp_add(aadd,badd,wl)
% 
% Fixed point subtraction out = a - b
% asub is fixed point input
% bsub is fixed point input
% wl is fractional word lenght
% return result of subtracting the inputs
%     
% Lennon Chaves
% September 29, 2016
% Manaus

fxp_asub= fxp_quantize(asub,wl);
fxp_bsub= fxp_quantize(bsub,wl);

fxp_num = fxp_quantize(fxp_asub - fxp_bsub, wl);

end
