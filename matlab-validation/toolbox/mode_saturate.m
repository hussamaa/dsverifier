function y = mode_saturate(value, n)
% 
% y = mode_saturate(value, n)
%
%  Function to saturate mode for arithmetic overflow
%  where,
%  'value' is number to be converted in case of arithmetic
%  'n' is word lenght implementation
%   the return 'y' is the output converted in saturate mode.
%
% Lennon Chaves
% October 04, 2016
% Manaus

y = value;

min = -1*(((2^n)-1));
max = ((2^n));

if value > max
    y = max;
elseif value < min
    y = min;
end

end