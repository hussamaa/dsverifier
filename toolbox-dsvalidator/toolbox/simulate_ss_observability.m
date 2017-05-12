function decision = simulate_ss_observability(sys)
% 
% Script developed to simulate the state-space observability property in counterexamples
% 
% For a LTI system in state-space format, SIMULATE_SS_OBSERVABILITY(sys)
% decides about the observability. 
% It returns decision = 1 if the system is observable, and 
% returns decision = 0 in other case.
% 
% Lennon Chaves
% May 12, 2017
% Manaus

A = sys.A;
B = sys.B;
C = sys.C;
D = sys.D;

[r,c] = size(A);

obsv_matrix = obsv(A,C);
n = rank(obsv_matrix);

if n == r
   decision=1; %The state-space system is OBSERVABLE
else
   decision=0; %The state-space system is NOT OBSERVABLE
end

end

