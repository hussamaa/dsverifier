A = [0 1;-25 -4]
B = [1 1;0 1]
C = [1 0;0 1]
D = [0 0;0 0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Ogata Controle Moderno pag 603