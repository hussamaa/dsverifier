J = [8 -3 -3; -3 8 -3; -3 -3 8];
F = 0.2*eye(3);
A = -J\F;
B = inv(J);
C = eye(3);
D = 0;
plant = ss(A,B,C,D);
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//http://www.mathworks.com/help/control/ug/mimo-state-space-models.html