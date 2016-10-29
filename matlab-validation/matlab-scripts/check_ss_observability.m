function decision = check_ss_observability(A,B,C,D,ts)
% 
% CHECK_SS_OBSERVABILITY(A,B,C,D,ts)
% 
% For a LTI system in state-space format, CHECK_SS_OBSERVABILITY(A,B,C,D,ts)
% decides about the observability. 
% It returns decision = 1 if the system is observable, and 
% returns decision = 0 in other case.
% 
% Lennon Chaves
% October 28, 2016
% Manaus

sys = ss(A,B,C,D);
sys = c2d(sys,ts,'zoh');

[r,c] = size(sys.A);

obsv_matrix = obsv(sys.A,sys.C);
n = rank(obsv_matrix);

if n == r
   decision=1;
else
   decision=0;
end

if decision
  disp('The state-space system is OBSERVABLE');
else
   disp('The state-space system is NOT OBSERVABLE');
end

end

