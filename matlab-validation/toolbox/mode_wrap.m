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

min = -1*(((2^n)-1));
max = ((2^n));

%if value > max
 %   y = max;
%elseif value < min
 %   y = min;
%end

range = max - min + 1;

kx = mod((value-min),range);

if (kx < 0)
    value = kx + 1 + max;
else
    value = kx + min;
end

y = value;

end