A = [0 1;-5 -2];
B = [0;3];
C = [0 1];
D = 0;
plant = ss(A,B,C,D);
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//http://www.mathworks.com/help/control/ug/state-space-models.html?searchHighlight=state%20space%20examples