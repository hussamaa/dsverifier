function dsv_validation(path, property, ovmode, rmode, filename)
%
% Script to run all steps to validate counterexamples
%
% Function: dsv_validation(path, property, ovmode, rmode, filename)
%
% To start the validation, the folder with all counterexamples should be
% informed.
%
% You need inform the path, e.g. 'home/user/dsv/counterexamples'
% The output files are generated at 'outputs' folder.
%
% property is the property of digital system to be validate:
%     'lc' is for limit cycle property
%     's' is for stability property
%     'm' is for minimum phase property
%     'o' is for overflow property
%
% ovmode is the overflow mode. The values could be:
%     'saturate' for saturate overflow
%     'wrap' for wrap around overflow
%     By default, the value is 'wrap'.
%
% rmode is the rounding mode. The values could be:
%     'round' to use round as rounded mode
%     'floor' to use floor as rounded mode
%      By default, the value is 'round'
%
% filename: the name of .MAT file generated as result from validation.
%      By default, the value is 'digital_system'
%
% Example of usage:
%  dsv_validation('/home/user/log/limit_cycle/','lc','wrap','round','ds_limit');
%  dsv_validation('/home/user/log/limit_cycle/','lc','saturate','floor','ds_limit');
%
% Lennon Chaves
% November 04, 2016
% Manaus, Brazil

global overflow_mode;
global round_mode;

overflow_mode = ovmode;
round_mode = rmode;

if isunix
disp('Running Automatic Validation...');
else
disp('Operating System not Supported for Automatic Validation Scripts!');
return
end


if (isempty(property))
    disp('Error. The parameter "property" should be "m","lc","o" or "s"!');
    return
elseif (strcmp(property,'m') || strcmp(property,'o') || strcmp(property,'lc') || strcmp(property,'s'))
else
    disp('Error. The parameter "property" should be "m","lc","o" or "s"!');
    return
end

if (isempty(path))
    disp('Error. You should inform a path of counterexamples!');
    return
end

if ~(strcmp(overflow_mode,'wrap') || strcmp(overflow_mode,'saturate'))
    overflow_mode = 'wrap';
end
if ~(strcmp(round_mode,'round') || strcmp(round_mode,'floor'))
    round_mode = 'round';
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
