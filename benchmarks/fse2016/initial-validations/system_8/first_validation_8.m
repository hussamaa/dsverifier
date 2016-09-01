[A,B,C,D] = tf2ss([16.635 -16.225],[1 3.3 10.82])
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//Digital Control Kannan Moudgalya pag. 507