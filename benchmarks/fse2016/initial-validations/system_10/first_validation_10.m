A = [0 1 0;0 0 1;-6 -11 -6]
B = [0;0;6]
C = [1,0,0]
D = [0.0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Ogata Controle Moderno pag 599