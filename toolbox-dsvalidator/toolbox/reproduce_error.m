function reproduce_error(path, varargin)
%
% Script developed to reproduce error property given a 'path' with all .out counterexamples.
%
% Function: reproduce_error(path)
%
% You need inform the 'path', that is a directory with all counterexamples stored in a .out files.
%
% The output is the feedback returned from simulation (successful or failed) and a .MAT file with counterexamples stored.
%
% Another usage form is adding other parameters (optional parameters) as follow:
%
% reproduce_error(path, ovmode, rmode, filename);
%
% Where:
%  ovmode is related to overflow mode and it could be: 'saturate' or 'wrap'. By default is 'wrap';
%  rmode is related to rounding mode and it could be: 'round' or 'floor'. By default is 'round';
%  filename is the name of counterexample .MAT file generated. By default is 'digital_system'.
%
%  Example of usage:
%
%  reproduce_error('/home/user/log/overflow/');
%
%  reproduce_error('/home/user/log/overflow/','saturate','floor','counterexample_file');
%
% Lennon Chaves
% November 16, 2016
% Manaus, Brazil

ovmode = '';
rmode = '';
filename = '';

nvar = nargin;

if nvar >= 2
if length(var{1}) > 0
 ovmode = var{1};
end
end

if nvar >= 3
if length(var{2}) > 0
 rmode = var{2};
end
end

if nvar >= 4
if length(var{3}) > 0
 filename = var{3};
end
end

property = 'e';

dsv_validation(path, property, ovmode, rmode, filename);

end
