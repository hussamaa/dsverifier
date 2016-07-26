%% Script to run all steps to validate counterexamples

% * All the output files are generated at 'outputs' folder.
%path = '/home/lennon/Development/matlab/VANT-Limit-Cycle/CT-Results-Completed';

%function to extract the parameters from counterexamples output. 
%You need inform the path, e.g. 'home/user/dsv/counterexamples'
run matlab-scripts/dsv_extraction(path);

%parsing the paramaters to variables workspace
run matlab-scripts/dsv_parser();

%simulation automatically of all counterexamples
run matlab-scripts/dsv_simulation();

%comparison between matlab and dsverifier outputs
run matlab-scripts/dsv_comparison();

%saving all variables created in a file .MAT in order to be used later.
save dsv_variables;
