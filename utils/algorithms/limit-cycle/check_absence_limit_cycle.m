function check_absence_limit_cycle(system)

disp('Running Exhaustively Absence of Limit Cycle');
disp(' ');

for i=1:length(system)
   check_exhaustively_limit_cycle(system(i).num, system(i).den, system(i).states , system(i).bits, 1 , i);
end

disp('Ending tests');
disp(' ');

end