%%%%%%%%%%
% 
% Longitudinal Motion of An Helicopter
% 
% Extracted from:
%   Feedback Control of Dynamics Systems, 6th ed
%   Franklin, G. F.; Powell, J. D.; Emami-Naemi
% Written by:
%   Iury Bessa
%   Manaus, 2016
%%%%%%%%%%
%%

g=9.81;
l=1;
num=9.8*[1,-0.5,6.3];
den=[1,0,g/l];
pendulum_tf_cont=tf(num,den);

%% Discretizing with Ts=1

ts=1;
pendulum_tf_disc1=c2d(pendulum_tf_cont,ts);
pendulum_ss_disc1=ss(pendulum_tf_disc1);

%% Discretizing with Ts=1.5

ts=1.5;
pendulum_tf_disc2=c2d(pendulum_tf_cont,ts);
pendulum_ss_disc2=ss(pendulum_tf_disc2);

%% Discretizing with Ts=0.5

ts=0.5;
pendulum_tf_disc3=c2d(pendulum_tf_cont,ts);
pendulum_ss_disc3=ss(pendulum_tf_disc3);

%% Discretizing with Ts=0.2

ts=0.2;
pendulum_tf_disc4=c2d(pendulum_tf_cont,ts);
pendulum_ss_disc4=ss(pendulum_tf_disc4);

%% Discretizing with Ts=0.1

ts=0.1;
pendulum_tf_disc5=c2d(pendulum_tf_cont,ts);
pendulum_ss_disc5=ss(pendulum_tf_disc5);

%% Discretizing with Ts=0.05

ts=0.05;
pendulum_tf_disc6=c2d(pendulum_tf_cont,ts);
pendulum_ss_disc6=ss(pendulum_tf_disc6);

%% Discretizing with Ts=0.01

ts=0.01;
pendulum_tf_disc7=c2d(pendulum_tf_cont,ts);
pendulum_ss_disc7=ss(pendulum_tf_disc7);

%% Discretizing with Ts=0.005

ts=0.005;
pendulum_tf_disc8=c2d(pendulum_tf_cont,ts);
pendulum_ss_disc8=ss(pendulum_tf_disc8);


%% Saving

save('benchmark_tf','pendulum_tf_disc1','pendulum_tf_disc2','pendulum_tf_disc3','pendulum_tf_disc4',...
    'pendulum_tf_disc5','pendulum_tf_disc6','pendulum_tf_disc7','pendulum_tf_disc8','-append')
save('benchmark_ss','pendulum_ss_disc1','pendulum_ss_disc2','pendulum_ss_disc3','pendulum_ss_disc4',...
    'pendulum_ss_disc5','pendulum_ss_disc6','pendulum_ss_disc7','pendulum_ss_disc8','-append')