function [output] = dsv_check_minimum_phase(system)
%
% Script developed to check minimum phase automatically all counterexamples 
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

    for i=1:length(rootsb)
        if abs(rootsb(i))>=1
	    %The system is a NON-MINIMUM-PHASE system
            decision = 0;
            break
        end
	%The system is a MINIMUM-PHASE system
        decision = 1;
    end

 if decision == 1
       output = 'Successfull';
 else
       output = 'Failed';
 end

end
