A = [-2 1 0;0 -2 1;0 0 -2]
B = [0;0;3]
C = [1 1 1]
D = [0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Ogata Controle Moderno pag 621