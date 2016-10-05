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

if (strcmp(p,'lc') || strcmp(p,'o') )

count = 0;

for i=1:system.impl.x_size
    fxp_out_ver = abs(system.output.output_verification(i));
    fxp_out_sim = abs(system.output.output_simulation(i));
    erro = abs(fxp_out_ver-fxp_out_sim);
    if erro == 0
       count = count + 1;
    elseif fxp_out_ver ~= 0
        erro = (erro/fxp_out_ver)*100;
        if floor(abs(erro)) <= 10
             count = count + 1;
        end
    end
    
end

    if count == system.impl.x_size
        output = 'Successful';
    else
        output = 'Failed';
    end

else

 if (strcmp(lower(strtrim(system.output.output_verification)),lower(strtrim(system.output.output_simulation))))
	output = 'Successful';
    else
        output = 'Failed';
 end

end

end
