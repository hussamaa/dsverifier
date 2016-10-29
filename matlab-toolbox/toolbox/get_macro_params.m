function extra_param = get_macro_params(n, var, type)

extra_param = '';
if(strcmp(type,'tf') || strcmp(type,'ss'))
  nvar = n;
elseif strcmp(type,'cl')
  nvar= n -1;
end

solver = ' --solver ';
omode = ' --overflow-mode ';
rmode = ' --rounding-mode ';
emode = ' --error-mode ';
timeout = ' --timeout ';

if nvar >= 5
if length(var{1}) > 0
extra_param = [extra_param solver var{1}];
end
end

if nvar >= 6
if length(var{2}) > 0
extra_param = [extra_param omode var{2}];
end
end

if nvar >= 7
if length(var{3}) > 0
extra_param = [extra_param rmode var{3}];
end
end

if nvar >= 8
if length(var{4}) > 0
extra_param = [extra_param emode var{4}];
end
end

if nvar >= 9
if length(var{5}) > 0
extra_param = [extra_param timeout var{5}];
end
end

end