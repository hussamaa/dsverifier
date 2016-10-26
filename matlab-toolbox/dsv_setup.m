function dsv_setup()

home = pwd;

cd ~/Documents/MATLAB/Add-Ons/Toolboxes/DSVerifier/code

current = pwd;

cd(home);

setenv('DSVERIFIER_HOME',current);

setenv('PATH', [getenv('PATH') ':' current]);

end

