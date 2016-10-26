function extra_param = get_macro_params(n, var, type)

extra_param = '';
if(strcmp(type,'tf'))
  nvar = n;
elseif strcmp(type,'cl')
  nvar= n -1;
end

switch(nvar)
    case 6
        if strcmp(var{1},'')
            extra_param = '';
        else
            extra_param = [' --overflow-mode ' var{1}];
        end
    case 7
        if strcmp(var{1},'') && strcmp(var{2},'')
            extra_param = '';
        elseif strcmp(var{1},'')
            extra_param = [' --rounding-mode ' var{2}];
        elseif strcmp(var{2},'')
            extra_param = [' --overflow-mode ' var{1}];
        else
            extra_param = [' --overflow-mode ' var{1} ' --rounding-mode ' var{2}];
        end
    case 8
         if strcmp(var{1},'') && strcmp(var{2},'') && strcmp(var{3},'')
            extra_param = '';
         elseif strcmp(var{1},'') && strcmp(var{2},'')
            extra_param = [' --error-mode ' var{3}];
         elseif strcmp(var{1},'') && strcmp(var{3},'')
            extra_param = [' --rounding-mode ' var{2}];
         elseif strcmp(var{2},'') && strcmp(var{3},'') 
            extra_param = [' --overflow-mode ' var{1}];
         elseif strcmp(var{1},'') 
            extra_param = [' --rounding-mode ' var{2} ' --error-mode ' var{3}];
         elseif strcmp(var{2},'') 
            extra_param = [' --overflow-mode ' var{1} ' --error-mode ' var{3}];
         elseif strcmp(var{3},'') 
            extra_param = [' --overflow-mode ' var{1} ' --rounding-mode ' var{2}];
         else
            extra_param = [' --overflow-mode ' var{1} ' --rounding-mode ' var{2} ' --error-mode ' var{3}];
         end
    case 9
         if strcmp(var{1},'') && strcmp(var{2},'') && strcmp(var{3},'') && strcmp(var{4},'')
            extra_param = '';
         elseif strcmp(var{1},'') && strcmp(var{2},'') && strcmp(var{3},'')
             extra_param = [' --timeout ' var{4}];
         elseif strcmp(var{1},'') && strcmp(var{3},'') && strcmp(var{4},'')
             extra_param = [' --rounding-mode ' var{2}];
         elseif strcmp(var{2},'') && strcmp(var{3},'')  && strcmp(var{4},'')
             extra_param = [' --overflow-mode ' var{1}];
         elseif strcmp(var{1},'') && strcmp(var{2},'')  && strcmp(var{4},'')
             extra_param = [' --error-mode ' var{3}];
         elseif strcmp(var{1},'') && strcmp(var{2},'')
             extra_param = [' --error-mode ' var{3} ' --timeout ' var{4}];
         elseif strcmp(var{1},'') && strcmp(var{3},'')
             extra_param = ['--rounding-mode ' var{2} ' --timeout ' var{4}];
         elseif strcmp(var{1},'') && strcmp(var{4},'')
             extra_param = [' --rounding-mode ' var{2} ' --error-mode ' var{3}];
         elseif strcmp(var{2},'') && strcmp(var{3},'')
             extra_param = [' --overflow-mode ' var{1} ' --timeout ' var{4}];
         elseif strcmp(var{2},'') && strcmp(var{4},'')
             extra_param = [' --overflow-mode ' var{1} ' --error-mode ' var{3}];
         elseif strcmp(var{3},'') && strcmp(var{4},'')
             extra_param = [' --overflow-mode ' var{1} ' --rounding-mode ' var{2}]; 
         elseif strcmp(var{1},'') 
            extra_param = [' --rounding-mode ' var{2} ' --error-mode ' var{3} ' --timeout ' var{4}];
         elseif strcmp(var{2},'') 
            extra_param = [' --overflow-mode ' var{1} ' --error-mode ' var{3} ' --timeout ' var{4}];
         elseif strcmp(var{3},'') 
            extra_param = [' --overflow-mode ' var{1} ' --rounding-mode ' var{2} ' --timeout ' var{4}];
         elseif strcmp(var{4},'') 
            extra_param = [' --overflow-mode ' var{1} ' --rounding-mode ' var{2} ' --timeout ' var{3}];
         else
            extra_param = [' --overflow-mode ' var{1} ' --rounding-mode ' var{2} ' --error-mode ' var{3} ' --timeout ' var{4}];
         end
end

end