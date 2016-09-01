r1 = 10
r2 = 20
c1 = 0.1
c2 = 0.1
A = [(-(1/(c1*r1))-(1/(c1*r2))) 1/(c1*r2); 1/(c2*r2) -1/(c2*r2)]
B = [1/(c1*r1);0]
C = [(-1/r1) 0]
D = [1/r1]
plant  = ss(A,B,C,D)
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//http://web.mit.edu/16.unified/www/FALL/signalssystems/Lecture11_12.pdf