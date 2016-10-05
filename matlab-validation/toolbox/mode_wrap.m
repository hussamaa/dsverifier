function y = mode_wrap(value, n)
% 
% y = mode_wrap(value, n)
%
%  Function to wrap around mode for arithmetic overflow
%  where,
%  'value' is number to be converted in case of arithmetic
%  'n' is word lenght implementation
%   the return 'y' is the output converted in wrap around mode.
%
% Lennon Chaves
% October 04, 2016
% Manaus

kX = value;
kLowerBound = -1*(((2^n)-1));
kUpperBound = ((2^n));

y = value;

if (value < kLowerBound) || (value > kUpperBound)

range_size = kUpperBound - kLowerBound + 1;

if (kX< kLowerBound)
    kX = kX + range_size * ((kLowerBound - kX) / range_size + 1);
end

y = kLowerBound + mod((kX - kLowerBound),range_size);
y = fxp_quantize(y,n);
end

end
