A = [-6 -5 -10;1 0 0;0 1 0]
B = [1;0;0]
C = [0 10 10]
D = [0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Ogata Controle Moderno pag 603