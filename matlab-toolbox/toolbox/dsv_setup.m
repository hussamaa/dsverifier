function dsv_setup()
% Setup the DSVERIFIER_HOME and model checkers visibility in a variable environment
%
% Function: DSV_SETUP()
%
% Author: Lennon Chaves
% Federal University of Amazonas
% October 2016
%

home = pwd;

cd ~/Documents/MATLAB/Add-Ons/Toolboxes/DSVerifier/code

current = pwd;

cd(home);

setenv('DSVERIFIER_HOME',current);

setenv('PATH', [getenv('PATH') ':' current]);

end

