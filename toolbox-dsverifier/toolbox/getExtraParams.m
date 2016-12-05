function extra_param = getExtraParams(n, var, type)
% Support function to get the extra params in order to add in command line
% during the execution
%
% Function: extra_param = getExtraParams(n, var, type)
%
%  n: number of arguments passed during the verification
%  var: vargin with all extra arguments
%  type: state-space, transfer-function or closed-loop
%
% Author: Lennon Chaves
% Federal University of Amazonas
% October 2016
%

extra_param = '';
if(strcmp(type,'tf') || strcmp(type,'ss'))
  nvar = n;
elseif strcmp(type,'cl')
  nvar= n -1;
end
bmc = ' --bmc ';
solver = ' --solver ';
omode = ' --overflow-mode ';
rmode = ' --rounding-mode ';
emode = ' --error-mode ';
timeout = ' --timeout ';

if nvar >= 4
if length(var{1}) > 0
extra_param = [extra_param bmc var{1}];
end
end

if nvar >= 5
if length(var{2}) > 0
extra_param = [extra_param solver var{2}];
end
end

if nvar >= 6
if length(var{3}) > 0
extra_param = [extra_param omode var{3}];
end
end

if nvar >= 7
if length(var{4}) > 0
extra_param = [extra_param rmode var{4}];
end
end

if nvar >= 8
if length(var{5}) > 0
extra_param = [extra_param emode var{5}];
end
end

if nvar >= 9
if length(var{6}) > 0
extra_param = [extra_param timeout var{6}];
end
end

end