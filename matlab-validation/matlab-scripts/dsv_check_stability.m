function [output] = dsv_check_stability(system)
%
% Script developed to check stability automatically all counterexamples 
% by realization form (DFI, DFII and TDFII)
%
% Give the system as a struct with all parameters of counterexample and
% simulate the system.
% Implementation based on function eiginside.m
% 
% Lennon Chaves
% September 29, 2016
% Manaus

rootsb=roots(system.sys.b);
rootsa=roots(system.sys.a);

decision = 0;

 for i=1:length(rootsa)
        if abs(rootsa(i))>=1
	    %The system is UNSTABLE
            decision = 0;
            break
        end
        %The system is STABLE
        decision = 1;    
 end
  
 if decision == 1
       output = 'Successfull';
 else
       output = 'Failed';
 end

end
