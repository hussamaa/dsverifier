function num_rounded = fxp_rounding (num, wl)
% 
% Function to perform a fixed point rounding function.
%
% Function: [num_rounded] = fxp_rounding(num , wl)
% 
% where:
% num is a input value to be rounded
% wl is fractional word lenght
%
% return the parameter 'num' rounded according to word length and
% implementation values.
%
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

global round_mode;

a = double(num);
l = double(wl);

if (strcmp(round_mode,'round'))
num_rounded =(2^(-1*l))*round(a*(2^l));
elseif (strcmp(round_mode,'floor'))
num_rounded =(2^(-1*l))*floor(a*(2^l));
elseif (strcmp(round_mode,'double'))
num_rounded =(2^(-1*l))*double(a*(2^l));
else
num_rounded =(2^(-1*l))*(a*(2^l));
end

end
