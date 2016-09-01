A = [0 1 0; 0 0 1; -13 -19 -7]
B = [0;0;1]
C = [26 13 0]
D = [0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)