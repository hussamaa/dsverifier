function decision = check_ss_stability (A,B,C,D,ts)
% 
% CHECK_SS_STABILITY(A,B,C,D,ts)
% 
% For a LTI system in state-space format, CHECK_SS_STABILITY(A,B,C,D,ts)
% decides about the stability. 
% It returns decision = 1 if the system presents stability, and 
% returns decision = 0 in other case.
% 
% Lennon Chaves
% October 28, 2016
% Manaus

sys = ss(A,B,C,D);
sys = c2d(sys,ts,'zoh');

eigs = eig(sys.A);

for i=1:length(eigs)

if abs(eigs(i))>=1
   decision=0;
   break;
end
decision=1;    
end

if decision
  disp('The state-space system is STABLE');
else
   disp('The state-space system is UNSTABLE');
end

end

