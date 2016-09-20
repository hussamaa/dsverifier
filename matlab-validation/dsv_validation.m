function system = dsv_validation(path)
%
% Script to run all steps to validate counterexamples
% output = dsv_validation(path)
% To start the validation, the folder with all counterexamples should be
% informed.
% You need inform the path, e.g. 'home/user/dsv/counterexamples'
% The output files are generated at 'outputs' folder.
%     
% Lennon Chaves
% September 20, 2016
% Manaus

addpath('matlab-scripts');
addpath('shell-scripts');

%function to extract the parameters from counterexamples output. 
dsv_extraction(path);

%parsing the paramaters to variables workspace
system = dsv_parser();

%simulation automatically of all counterexamples
for i=1:length(system)
    output = dsv_simulation(system(i));
    system(i).output_simulation = output;
end

%comparison between matlab and dsverifier outputs
for i=1:length(system)
    status = dsv_comparison(system(i));
    system(i).status = status;
end

%saving all variables created in a file .MAT in order to be used later.
save ('dsv_variables.mat','system');
end