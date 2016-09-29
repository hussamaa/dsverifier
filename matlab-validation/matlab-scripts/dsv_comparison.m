function [output] = dsv_comparison(system, p)
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

if (p == 'lc')

count = 0;

for i=1:system.impl.x_size

    if system.output.output_verification(i) == system.output.output_simulation(i)
       count = count + 1;
    end
    
end

    if count == system.impl.x_size
        output = 'Successful';
    else
        output = 'Failed';
    end

else

 if (strcmp(system.output.output_verification,system.output.output_simulation))
	output = 'Successful';
    else
        output = 'Failed';
 end

end

end
