function dsv_extraction(directory, p)

%
% function dsv_extraction(directory, p)
% directory should be the path with all counterexamples in .out files.
%
% Script to extraction from counterexamples folder all parameters necessaries
% for validation and reproduction in MATLAB
%     
% Lennon Chaves
% September 29, 2016
% Manaus

sh = 'sh';
cp = 'cp';
%extraction of parameters

if (p == 'lc')

script1 = 'dsverifier-directory-data-extractor-script.sh';
command = [sh ' ' script1 ' ' directory];
system(command);

%copying files to matlab directory
command = [cp ' ' directory '/dsv_counterexample_parameters.txt' ' dsv_counterexample_parameters.txt'];
system(command);

else

script2 = 'dsverifier-restricted-counterexample-extractor-script.sh';
command = [sh ' ' script2 ' ' directory];
system(command);

%copying files to matlab directory
command = [cp ' ' directory '/dsv_counterexample_parameters.txt' ' dsv_counterexample_parameters.txt'];
system(command);

end

end
