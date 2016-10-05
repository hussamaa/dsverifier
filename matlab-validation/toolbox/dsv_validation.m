function digital_system = dsv_validation(path, property, filename)
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

digital_system = [];

if isunix
display('Running Automatic Validation...');
else
display('Operating System not Supported for Automatic Validation Scripts!');
return
end


if (isempty(property))
    display('Error. The parameter "property" should be "m","lc","o" or "s"!');
    return
elseif (strcmp(property,'m') || strcmp(property,'o') || strcmp(property,'lc') || strcmp(property,'s'))
else
    display('Error. The parameter "property" should be "m","lc","o" or "s"!');
    return
end

if (isempty(path))
    display('Error. You should inform a path of counterexamples!');
    return
end

%function to extract the parameters from counterexamples output. 
dsv_extraction(path, property);

%parsing the paramaters to variables workspace
digital_system = dsv_parser(property);

%simulation automatically of all counterexamples

for i=1:length(digital_system)
  [output, time_execution] = dsv_simulation(digital_system(i), property);
  digital_system(i).output.output_simulation = output;
  digital_system(i).output.time_execution = time_execution;
end
	
%comparison between matlab and dsverifier outputs
for i=1:length(digital_system)
    status = dsv_comparison(digital_system(i), property);
    digital_system(i).output.status = status;
    digital_system(i).status = status;
end

%report for user
dsv_report(digital_system);

%saving all variables created in a file .MAT in order to be used later.

fname = 'counterexamples.mat';
varname = 'digital_system';

if length(filename) > 0
fname = [filename '.mat'];
rname = [filename,'= digital_system;'];
eval(rname);
varname = filename;
end

save (fname,varname);

end
