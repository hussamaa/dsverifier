A = [-1.0, 1.0, 0.0; 0.0, -1.0, 0.0; 0.0, 0.0, -3.0]
B = [0.0; 1.0; 1.0]
C = [1.5, 1.25, -0.25]
D = [0.0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)