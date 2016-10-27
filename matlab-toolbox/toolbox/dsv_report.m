function output = dsv_report(output, representation)

global property;
fid = fopen(output);
tline = fgetl(fid);

while ischar(tline)
if strcmp(strtrim(tline),'VERIFICATION SUCCESSFUL')
    output = 'VERIFICATION SUCCESSFUL';
elseif strcmp(strtrim(tline),'VERIFICATION FAILED')
    output = 'VERIFICATION FAILED';
else
    output = 'VERIFICATION ERROR';
end

tline = fgetl(fid);
end

is_closed_loop = 0;

if strcmp(representation,'cl')
    is_closed_loop = 1;
end

is_state_space = 0;
if strcmp(representation,'ss')
    is_state_space = 1;
end

if (is_closed_loop == 0) && (is_state_space == 0)
    
if strcmp(output,'VERIFICATION FAILED')
    home = pwd;
    cd ~/Documents/MATLAB/Add-Ons/Toolboxes/DSVerifier/code
    sh = 'sh';
    directory = home;

    if strcmp(property,'OVERFLOW') || strcmp(property,'LIMIT_CYCLE')
        script1 = 'dsverifier-directory-data-extractor-script.sh';
        command = [sh ' ' script1 ' ' directory];
        system(command);
    else
        script2 = 'dsverifier-restricted-counterexample-extractor-script.sh';
        command = [sh ' ' script2 ' ' directory];
        system(command);
    end
    
    counterexample = gen_counterexample(property, directory);
    cd(home);
    
    save ('counterexample.mat', 'counterexample');

end

end


end

