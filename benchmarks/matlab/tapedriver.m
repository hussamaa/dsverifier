%%%%%%%%%%
% 
% Computer Tape Driver
% 
% Extracted from:
%   Feedback Control of Dynamics Systems, 6th ed
%   Franklin, G. F.; Powell, J. D.; Emami-Naemi
% Written by:
%   Iury Bessa
%   Manaus, 2016
%%%%%%%%%%
%%

J1=5e-5;
B1=1e-2;
r1=2e-2;
Kt=3e-2;
K=2e4;
B=20;
r2=2e-2;
J2=2e-5;
B2=2e-2;
F=6;

num=(Kt*r1)*[J2,(B2+(r2^2)*B),(r2^2)*K];
den=[J1*J2,J1*B2+B1*J2+(r2^2)*J1*B+(r1^2*J2*B),B1*B2+(r2^2)*J1*K+(r2^2)*B1*B+(r1^2)*J2*K+(r1^2)*B2*B,(r2^2)*B1*K+(r1^2)*B2*K];
tapedriver_tf_cont=tf(num,den);

%% Discretizing with Ts=1

ts=1;
tapedriver_tf_disc1=c2d(tapedriver_tf_cont,ts);
tapedriver_ss_disc1=ss(tapedriver_tf_disc1);

%% Discretizing with Ts=0.001

ts=1.5;
tapedriver_tf_disc2=c2d(tapedriver_tf_cont,ts);
tapedriver_ss_disc2=ss(tapedriver_tf_disc2);

%% Discretizing with Ts=0.5

ts=0.5;
tapedriver_tf_disc3=c2d(tapedriver_tf_cont,ts);
tapedriver_ss_disc3=ss(tapedriver_tf_disc3);

%% Discretizing with Ts=0.2

ts=0.2;
tapedriver_tf_disc4=c2d(tapedriver_tf_cont,ts);
tapedriver_ss_disc4=ss(tapedriver_tf_disc4);

%% Discretizing with Ts=0.1

ts=0.1;
tapedriver_tf_disc5=c2d(tapedriver_tf_cont,ts);
tapedriver_ss_disc5=ss(tapedriver_tf_disc5);

%% Discretizing with Ts=0.05

ts=0.05;
tapedriver_tf_disc6=c2d(tapedriver_tf_cont,ts);
tapedriver_ss_disc6=ss(tapedriver_tf_disc6);

%% Discretizing with Ts=0.01

ts=0.01;
tapedriver_tf_disc7=c2d(tapedriver_tf_cont,ts);
tapedriver_ss_disc7=ss(tapedriver_tf_disc7);

%% Discretizing with Ts=0.005

ts=0.01;
tapedriver_tf_disc8=c2d(tapedriver_tf_cont,ts);
tapedriver_ss_disc8=ss(tapedriver_tf_disc8);


%% Saving

save('benchmark_tf','tapedriver_tf_disc1','tapedriver_tf_disc2','tapedriver_tf_disc3','tapedriver_tf_disc4',...
    'tapedriver_tf_disc5','tapedriver_tf_disc6','tapedriver_tf_disc7','tapedriver_tf_disc8','-append')
save('benchmark_ss','tapedriver_ss_disc1','tapedriver_ss_disc2','tapedriver_ss_disc3','tapedriver_ss_disc4',...
    'tapedriver_ss_disc5','tapedriver_ss_disc6','tapedriver_ss_disc7','tapedriver_ss_disc8','-append')