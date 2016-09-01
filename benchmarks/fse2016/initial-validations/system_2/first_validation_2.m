A = [-6.0, -11.0, -6.0; 1.0, 0.0, 0.0; 0.0, 1.0, 0.0]
B = [1.0; 0.0; 0.0]
C = [1.0, 9.0, 20.0]
D = [0.0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)