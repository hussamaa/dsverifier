A = [0 1;-2 -3]
B = [0;1]
C = [0 1]
D = [0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Ogata Controle Moderno pag 610