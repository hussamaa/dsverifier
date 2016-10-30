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

user = userpath;

install_folder = [user '/Add-Ons/Toolboxes/DSVerifier/code'];

cd(install_folder);

current = pwd;

cd(home);

setenv('DSVERIFIER_HOME',current);

setenv('PATH', [getenv('PATH') ':' current]);

end

