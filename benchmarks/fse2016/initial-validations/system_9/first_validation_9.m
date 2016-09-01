A = [-1.0,0.0;0.0,-2.0]
B = [1.0;1.0]
C = [2.0,-1]
D = [0.0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Ogata Controle Moderno pag 598