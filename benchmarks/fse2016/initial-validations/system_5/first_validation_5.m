A = [-1.0, 0.0, 0.0; 0.0, -2.0, 0.0; 0.0, 0.0, -3.0]
B = [1.0; 1.0; 1.0]
C = [6.0, -6.0, 1.0]
D = [0.0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)