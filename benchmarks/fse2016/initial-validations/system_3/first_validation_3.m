J = 0.01
Kb = 0.01
Kf = 0.1
Km = 0.01
L = 0.5
R = 1
A_motor = [-Kf/J Km/J; -Kb/L -R/L]
B_motor = [0;1/L]
C_motor = [1 0]
D_motor = [0]
plant = ss(A_motor,B_motor,C_motor,D_motor)
isstable(plant)
rank(ctrb(A_motor,B_motor))
rank(obsv(A_motor,C_motor))
step(plant)