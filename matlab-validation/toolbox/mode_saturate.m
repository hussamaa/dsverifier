function y = mode_saturate(value, n, l)
% 
%  Function to saturate mode for arithmetic overflow
%
% y = mode_saturate(value, n)
%
%  where,
%  'value' is number to be converted in case of arithmetic
%  'n' is integer bits implementation
%  'l' is fractionary bits implementation
%   the return 'y' is the output converted in saturate mode.
%
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

y = value;

min = -1*(2^(n-1));
max = (2^(n-1)-2^(-1*l));

if value > max
    y = max;
elseif value < min
    y = min;
end

end
