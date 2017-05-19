function validationExtraction(directory, p)

%
% Function to extract all counterexamples from .out files generated by DSVerifier
% Script to extraction from counterexamples folder all parameters necessaries
% for validation and reproduction in MATLAB
%
% Function: validationExtraction(directory, p)
%
% Where 'directory' should be the path with all counterexamples inside .out files.
% And the parameter 'p' is the property to be analyzed: (m) for minimum phase, (s) for stability, (o) for overflow and (lc) for limit cycle.
% (scl) for stability in closed-loop systems, (sss) for stability in state-space format, (ssc) for controllability in state-space format and (sso) for observability in state-space format.
%
% Federal University of Amazonas
% May 15, 2017
% Manaus, Brazil

sh = 'sh';
cp = 'cp';

current =  pwd;

user = userpath;
install_folder = [user '/Add-Ons/Toolboxes/DSValidator/code'];
cd(install_folder);

%extraction of parameters

if (strcmp(p,'lc') || strcmp(p,'o')) %for overflow and lco only.
    
    script1 = 'dsverifier-directory-data-extractor-script.sh';
    command = [sh ' ' script1 ' ' directory];
    system(command);
    
    %copying files to matlab directory
    command = [cp ' ' directory '/dsv_counterexample_parameters.txt' ' dsv_counterexample_parameters.txt'];
    system(command);
    
else %for all the others properties in transfer-function format.
    
    script2 = 'dsverifier-restricted-counterexample-extractor-script.sh';
    command = [sh ' ' script2 ' ' directory];
    system(command);
    
    %copying files to matlab directory
    command = [cp ' ' directory '/dsv_counterexample_parameters.txt' ' dsv_counterexample_parameters.txt'];
    system(command);
    
end

cd(current);

end
