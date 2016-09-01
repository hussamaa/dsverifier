A = [-1 -0.5;1 0]
B = [0.5;0]
C = [1 0]
D = [0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Ogata Controle Moderno pag 638