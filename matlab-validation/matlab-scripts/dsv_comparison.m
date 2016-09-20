function [output] = dsv_comparison(system)
%
% Function [output] = dsv_comparison(system)
% Script to verify and compare the results between MATLAB and DSVerifier
% Give the system as input on this function and check if the outputs of
% MATLAB and DSVerifier are the same
%
%     
% Lennon Chaves
% September 20, 2016
% Manaus

count = 0;

for i=1:system.x_size

    if system.output_verification(i) == system.output_simulation(i)
       count = count + 1;
    end
    
end

    if count == system.x_size
        output = 'Successful';
    else
        output = 'Failed';
    end

end