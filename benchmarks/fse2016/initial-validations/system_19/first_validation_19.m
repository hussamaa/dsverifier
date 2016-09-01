[A,B,C,D] = tf2ss([1 6],[1 5 6])
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Ogata Controle Moderno pag 654