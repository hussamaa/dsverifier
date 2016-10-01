function digital_system = dsv_validation(path, p)
%
% Script to run all steps to validate counterexamples
% digital_system = dsv_validation(path,p)
% To start the validation, the folder with all counterexamples should be
% informed.
% You need inform the path, e.g. 'home/user/dsv/counterexamples'
% The output files are generated at 'outputs' folder.
% p is the property to be validate:
%     'lc' is for limit cycle property
%     's' is for stability property
%     'm' is for minimum phase property
%     'o' is for overflow property
%
% Lennon Chaves
% September 20, 2016
% Manaus

addpath('matlab-scripts');
addpath('shell-scripts');

digital_system = [];

if isunix
display('Running Automatic Validation...');
else
display('Operating System not Supported for Automatic Validation Scripts!');
return
end


if (isempty(p))
    display('Error. The parameter "p" should be "m","lc","o" or "s"!');
    return
elseif (strcmp(p,'m') || strcmp(p,'o') || strcmp(p,'lc') || strcmp(p,'s'))
else
    display('Error. The parameter "p" should be "m","lc","o" or "s"!');
    return
end

if (isempty(path))
    display('Error. You should inform a path of counterexamples!');
    return
end

%function to extract the parameters from counterexamples output. 
dsv_extraction(path, p);

%parsing the paramaters to variables workspace
digital_system = dsv_parser(p);

%simulation automatically of all counterexamples

for i=1:length(digital_system)
  [output, time_execution] = dsv_simulation(digital_system(i), p);
  digital_system(i).output.output_simulation = output;
  digital_system(i).output.time_execution = time_execution;
end
	
%comparison between matlab and dsverifier outputs
for i=1:length(digital_system)
    status = dsv_comparison(digital_system(i), p);
    digital_system(i).output.status = status;
    digital_system(i).status = status;
end

%saving all variables created in a file .MAT in order to be used later.
save ('dsv_variables.mat','digital_system');

end
