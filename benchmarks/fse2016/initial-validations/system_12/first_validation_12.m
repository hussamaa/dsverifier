A = [0 1 0 ;0 0 1; -5.008 -25.1026 -5.03247]
B = [0;25.04;-121.005]
C = [1 0 0]
D = [0]
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Ogata Controle Moderno pag 603