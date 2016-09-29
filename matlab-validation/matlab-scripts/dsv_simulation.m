function [output] = dsv_simulation(system,p)
%
% Script developed to simulate automatically all counterexamples 
% by realization form (DFI, DFII and TDFII)
%
% Give the system as a struct with all parameters of counterexample and
% simulate the system.
% 
% Lennon Chaves
% September 20, 2016
% Manaus

  switch p
	case 'lc' 
    	   output = dsv_check_limit_cycle(system);
	case 's' 
    	   output = dsv_check_stability(system);
	case 'm' 
    	   output = dsv_check_minimum_phase(system);
	case 'o' 
    	   output = dsv_check_overflow(system);
	otherwise
           warning('Unexpected property or error during the automatic validation.')
  end

end
