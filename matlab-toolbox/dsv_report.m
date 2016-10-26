function output = dsv_report(output)

global property;
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

if strcmp(output,'VERIFICATION FAILED')
    sh = 'sh';
    directory = pwd;

    if strcmp(property,'OVERFLOW') || strcmp(property,'LIMIT_CYCLE')
        script1 = 'dsverifier-directory-data-extractor-script.sh';
        command = [sh ' ' script1 ' ' directory];
        system(command);
    else
        script2 = 'dsverifier-restricted-counterexample-extractor-script.sh';
        command = [sh ' ' script2 ' ' directory];
        system(command);
    end
    
    counterexample = gen_counterexample(property);
    save ('counterexample.mat', 'counterexample');
end
%TO DO: .MAT File, Extract counterexample
end

