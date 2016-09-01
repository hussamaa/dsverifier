A = [-2.0,-1.0;1.0,0.0]
B = [1.0;0.0]
C = [1.0,2.0]
D = [1.0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)