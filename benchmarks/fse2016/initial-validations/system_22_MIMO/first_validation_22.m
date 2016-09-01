A = [-0.0558   -0.9968    0.0802    0.0415
	 0.5980   -0.1150   -0.0318         0
	 -3.0500    0.3880   -0.4650         0
	 0    0.0805    1.0000         0];
B = [ 0.0073         0
	 -0.4750    0.0077
	 0.1530    0.1430
	 0         0];
C = [0     1     0     0
	 0     0     0     1];
D = [0     0
	 0     0];
plant = ss(A,B,C,D);
isstable(plant)
rank(ctrb(A,B))
rank(obsv(A,C))
step(plant)

//http://www.mathworks.com/help/control/ug/mimo-state-space-models.html