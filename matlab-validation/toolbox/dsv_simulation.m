function [output, time_execution] = dsv_simulation(system,p)
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
    	  [output, time_execution]  = dsv_check_limit_cycle(system);
	case 's' 
    	  [output, time_execution]  = dsv_check_stability(system);
	case 'm' 
    	  [output, time_execution]  = dsv_check_minimum_phase(system);
	case 'o' 
    	  [output, time_execution]  = dsv_check_overflow(system);
	otherwise
           warning('Unexpected property or error during the automatic validation.')
  end

end
