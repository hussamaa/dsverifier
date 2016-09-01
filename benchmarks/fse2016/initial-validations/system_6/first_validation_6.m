A = [-5.0, 0.0, 0.0, 0.0; 0.0, -10.0, 0.0, 0.0; 0.0, 0.0, 0.0, 1.0; 0.0, 0.0, -2.0, -2.0]
B = [1.0; 1.0; 0.0; 1.0]
C = [2.0 03.0 8.0 8.0]
D = [0.0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)