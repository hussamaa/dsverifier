%% Script execute the validation automatically for all counterexamples
function dsv_validation(directory)

sh = 'sh';
cp = 'cp';
%extraction of parameters

script1 = 'shell-scripts/dsverifier-directory-data-extractor-script.sh';
command = [sh ' ' script1 ' ' directory];
system(command);

%extraction of outputs
script2 = 'shell-scripts/dsverifier-directory-outputs-extractor-script.sh';
command = [sh ' ' script2 ' ' directory];
system(command);

%copying files to matlab directory
command = [cp ' ' directory '/dsv_counterexample_parameters.txt' ' dsv_counterexample_parameters.txt'];
system(command);
command = [cp ' ' directory '/dsv_counterexamples_outputs.txt' ' dsv_counterexamples_outputs.txt'];
system(command);

%parsing the paramaters to variables workspace
dsv_parser();
%simulation automatically of all counterexamples
%dsv_simulation();

%comparation between matlab and dsverifier outputs
script3 = 'shell-scripts/dsverifier-matlab-comparison-script.sh';
command = [sh ' ' script3 ' ' 'dsv_matlab_filter_outputs.txt' ' ' 'dsv_counterexamples_outputs.txt'];
system(command);

end