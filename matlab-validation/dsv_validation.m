%path = '/home/lennon/Development/matlab/VANT-Limit-Cycle/CT-Results-Completed';
sh = 'sh';
cp = 'cp';

%function to extract the parameters from counterexamples output
dsv_extraction(path);

%parsing the paramaters to variables workspace
dsv_parser();

%simulation automatically of all counterexamples
dsv_simulation();

%comparation between matlab and dsverifier outputs
script3 = 'shell-scripts/dsverifier-matlab-comparison-script.sh';
command = [sh ' ' script3 ' ' 'dsv_matlab_filter_outputs.txt' ' ' 'dsv_counterexamples_outputs.txt'];
system(command);

%saving all variables created in a file .MAT in order to be used later.
save dsv_variables;