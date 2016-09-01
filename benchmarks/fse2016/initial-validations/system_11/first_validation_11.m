A = [0 1 0;0 0 1;-10 -5 -6]
B = [0;10;-50]
C = [1 0 0]
D = [0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Ogata Controle Moderno pag 602