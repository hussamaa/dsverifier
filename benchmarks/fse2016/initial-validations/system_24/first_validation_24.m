n=[1 1];
d=[1 1 10];
[A,B,C,D]=tf2ss(n,d);
plant(A,B,C,D)
plant = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//http://www.mathworks.com/help/control/ref/ss.html