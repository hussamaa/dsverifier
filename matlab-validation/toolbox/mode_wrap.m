function y = mode_wrap(value, n, l)
% 
%  Function to wrap around mode for arithmetic overflow
%
% y = mode_wrap(value, n)
%
%  where,
%  'value' is number to be converted in case of arithmetic
%  'n' is integer bits implementation
%  'l' is fractionary bits implementation
%   the return 'y' is the output converted in wrap around mode.
%
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil


kX = value;
kLowerBound = -1*(2^(n-1));
kUpperBound = (2^(n-1)-2^(-1*l));

y = value;

if (value < kLowerBound) || (value > kUpperBound)

range_size = kUpperBound - kLowerBound + 1;

if (kX< kLowerBound)
    kX = kX + range_size * ((kLowerBound - kX) / range_size + 1);
end

y = kLowerBound + mod((kX - kLowerBound),range_size);

end

y = fxp_quantize(y,l);

end
