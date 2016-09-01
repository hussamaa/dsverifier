A = [-2 0; 0 -3]
B = [1;1]
C = [5 -13]
D = [2]
plant = ss(A,B,C,D);
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

// Example 8.20 pag. 321 Digital Control Engineering M. Sam Fadali