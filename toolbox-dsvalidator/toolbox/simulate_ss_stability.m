function decision = simulate_ss_stability (sys,K,type)
% 
% SIMULATE_SS_STABILITY(sys,K,type)
% 
% For a LTI system in state-space format, CHECK_SS_STABILITY(sys,K,type)
% decides about the stability. 
% where 'sys' is a state-space system, 'K' is the feedback matrix and 'type' must be 'cl'
% for closed-loop systems.
%
% It returns decision = 1 if the system presents stability, and 
% returns decision = 0 in other case.
% 
% Lennon Chaves
% May 12, 2017
% Manaus

A = sys.A;
B = sys.B;
C = sys.C;
D = sys.D;

if strcmp(type,'cl') %closed-loop system
    F = A-B*K;
else
    F = A;
end

eigs = eig(F);

for i=1:length(eigs)

if abs(real(eigs(i)))>1 %checking if roots are inside the unitary cycle.
   decision=0; %The state-space system is UNSTABLE
   break;
end
decision=1;    %The state-space system is STABLE
end

end

