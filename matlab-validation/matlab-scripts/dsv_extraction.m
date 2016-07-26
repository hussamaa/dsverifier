%% Script to extraction from counterexamples folder all parameters necessaries
%% for validation and reproduction in MATLAB

function dsv_extraction(directory)

sh = 'sh';
cp = 'cp';
%extraction of parameters

script1 = '../shell-scripts/dsverifier-directory-data-extractor-script.sh';
command = [sh ' ' script1 ' ' directory];
system(command);

%extraction of outputs
script2 = '../shell-scripts/dsverifier-directory-outputs-extractor-script.sh';
command = [sh ' ' script2 ' ' directory];
system(command);

%output directory
command = ['mkdir' ' ../outputs'];
system(command);

%copying files to matlab directory
command = [cp ' ' directory '/dsv_counterexample_parameters.txt' ' ../outputs/dsv_counterexample_parameters.txt'];
system(command);
command = [cp ' ' directory '/dsv_counterexamples_outputs.txt' ' ../outputs/dsv_counterexamples_outputs.txt'];
system(command);

end
