function fxp_num = fxp_sub(asub, bsub, wl)
%
% Function to perform a fixed point subtraction out = a - b
% 
% Function: [fxp_num]=fxp_add(aadd,badd,wl)
% 
% where:
% asub is fixed point input
% bsub is fixed point input
% wl is fractional word lenght
%
% return result of subtracting the inputs
%     
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

fxp_asub= fxp_quantize(asub,wl);
fxp_bsub= fxp_quantize(bsub,wl);

fxp_num = fxp_quantize(fxp_asub - fxp_bsub, wl);

end
