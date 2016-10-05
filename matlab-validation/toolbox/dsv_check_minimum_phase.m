function [output, time_execution] = dsv_check_minimum_phase(system)
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

tic

if (system.impl.delta ~= 0)
[Da, Db] = deltapoly(system.sys.b, system.sys.a, system.impl.delta);
rootsb = roots(Db);
rootsa = roots(Da);
else 
rootsb=roots(system.sys.b);
rootsa=roots(system.sys.a);
end

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

 if decision == 0
       output = 'Successful';
 else
       output = 'Failed';
 end

 time_execution = toc;
 
end
