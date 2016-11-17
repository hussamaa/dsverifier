function decision = check_ss_controllability (A,B,C,D,ts)
% 
% CHECK_SS_CONTROLLABILITY(A,B,C,D,ts)
% 
% For a LTI system in state-space format, CHECK_SS_CONTROLLABILITY(A,B,C,D,ts)
% decides about the controlability. 
% It returns decision = 1 if the system is controllable, and 
% returns decision = 0 in other case.
% 
% Lennon Chaves
% October 28, 2016
% Manaus

sys = ss(A,B,C,D);
sys = c2d(sys,ts,'zoh');

[r,c] = size(sys.A);

ctrb_matrix = ctrb(sys.A,sys.B);
n = rank(ctrb_matrix);

if n == c
   decision=1;
else
   decision=0;
end

if decision
  disp('The state-space system is CONTROLLABLE');
else
   disp('The state-space system is NOT CONTROLLABLE');
end

end

