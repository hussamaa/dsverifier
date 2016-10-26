function output = dsv_report(output)

fid = fopen(output);
tline = fgetl(fid);

while ischar(tline)
if strcmp(strtrim(tline),'VERIFICATION SUCCESSFUL')
    output = 'VERIFICATION SUCCESSFUL';
elseif strcmp(strtrim(tline),'VERIFICATION FAILED')
    output = 'VERIFICATION FAILED';
end

tline = fgetl(fid);
end

%TO DO: .MAT File, Extract counterexample
end

