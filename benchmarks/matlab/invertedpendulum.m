%%%%%%%%%%
% 
% Inverted Cart Pendulum
% 
% Extracted from:
%   Feedback Control of Dynamics Systems, 6th ed
%   Franklin, G. F.; Powell, J. D.; Emami-Naemi
% Written by:
%   Iury Bessa
%   Manaus, 2016
%%%%%%%%%%
%%
mp=0.1;
mc=0.2;

num=[1];
den=[1,0,-1];
invpendulum_pendang_tf_cont=tf(num,den);

num=[1,(-1+(3*mp/(4*mc+4*mp)))];
den=[conv([1,0,0],[1,0,-1])];
invpendulum_cartpos_tf_cont=tf(num,den);

%% Discretizing with Ts=0.5

ts=0.5;
invpendulum_pendang_tf_disc1=c2d(invpendulum_pendang_tf_cont,ts,'matched');
invpendulum_cartpos_tf_disc1=c2d(invpendulum_cartpos_tf_cont,ts,'matched');
invpendulum_pendang_ss_disc1=ss(invpendulum_pendang_tf_disc1);
invpendulum_cartpos_ss_disc1=ss(invpendulum_cartpos_tf_disc1);

%% Discretizing with Ts=0.2

ts=0.2;
invpendulum_pendang_tf_disc2=c2d(invpendulum_pendang_tf_cont,ts,'matched');
invpendulum_cartpos_tf_disc2=c2d(invpendulum_cartpos_tf_cont,ts,'matched');
invpendulum_pendang_ss_disc2=ss(invpendulum_pendang_tf_disc2);
invpendulum_cartpos_ss_disc2=ss(invpendulum_cartpos_tf_disc2);

%% Discretizing with Ts=0.1

ts=0.1;
invpendulum_pendang_tf_disc3=c2d(invpendulum_pendang_tf_cont,ts,'matched');
invpendulum_cartpos_tf_disc3=c2d(invpendulum_cartpos_tf_cont,ts,'matched');
invpendulum_pendang_ss_disc3=ss(invpendulum_pendang_tf_disc3);
invpendulum_cartpos_ss_disc3=ss(invpendulum_cartpos_tf_disc3);

%% Discretizing with Ts=0.05

ts=0.05;
invpendulum_pendang_tf_disc4=c2d(invpendulum_pendang_tf_cont,ts,'matched');
invpendulum_cartpos_tf_disc4=c2d(invpendulum_cartpos_tf_cont,ts,'matched');
invpendulum_pendang_ss_disc4=ss(invpendulum_pendang_tf_disc4);
invpendulum_cartpos_ss_disc4=ss(invpendulum_cartpos_tf_disc4);

%% Discretizing with Ts=0.01

ts=0.01;
invpendulum_pendang_tf_disc5=c2d(invpendulum_pendang_tf_cont,ts,'matched');
invpendulum_cartpos_tf_disc5=c2d(invpendulum_cartpos_tf_cont,ts,'matched');
invpendulum_pendang_ss_disc5=ss(invpendulum_pendang_tf_disc5);
invpendulum_cartpos_ss_disc5=ss(invpendulum_cartpos_tf_disc5);

%% Discretizing with Ts=0.005

ts=0.005;
invpendulum_pendang_tf_disc6=c2d(invpendulum_pendang_tf_cont,ts,'matched');
invpendulum_cartpos_tf_disc6=c2d(invpendulum_cartpos_tf_cont,ts,'matched');
invpendulum_pendang_ss_disc6=ss(invpendulum_pendang_tf_disc6);
invpendulum_cartpos_ss_disc6=ss(invpendulum_cartpos_tf_disc6);

%% Discretizing with Ts=0.001

ts=0.001;
invpendulum_pendang_tf_disc7=c2d(invpendulum_pendang_tf_cont,ts,'matched');
invpendulum_cartpos_tf_disc7=c2d(invpendulum_cartpos_tf_cont,ts,'matched');
invpendulum_pendang_ss_disc7=ss(invpendulum_pendang_tf_disc7);
invpendulum_cartpos_ss_disc7=ss(invpendulum_cartpos_tf_disc7);

%% Discretizing with Ts=0.0005

ts=0.0005;
invpendulum_pendang_tf_disc8=c2d(invpendulum_pendang_tf_cont,ts,'matched');
invpendulum_cartpos_tf_disc8=c2d(invpendulum_cartpos_tf_cont,ts,'matched');
invpendulum_pendang_ss_disc8=ss(invpendulum_pendang_tf_disc8);
invpendulum_cartpos_ss_disc8=ss(invpendulum_cartpos_tf_disc8);

%% Saving

save('benchmark_tf','invpendulum_pendang_tf_disc1','invpendulum_pendang_tf_disc2','invpendulum_pendang_tf_disc3','invpendulum_pendang_tf_disc4',...
    'invpendulum_pendang_tf_disc5','invpendulum_pendang_tf_disc6','invpendulum_pendang_tf_disc7','invpendulum_pendang_tf_disc8','-append')

save('benchmark_tf','invpendulum_cartpos_tf_disc1','invpendulum_cartpos_tf_disc2','invpendulum_cartpos_tf_disc3','invpendulum_cartpos_tf_disc4',...
    'invpendulum_cartpos_tf_disc5','invpendulum_cartpos_tf_disc6','invpendulum_cartpos_tf_disc7','invpendulum_cartpos_tf_disc8','-append')

save('benchmark_ss','invpendulum_pendang_ss_disc1','invpendulum_pendang_ss_disc2','invpendulum_pendang_ss_disc3','invpendulum_pendang_ss_disc4',...
    'invpendulum_pendang_ss_disc5','invpendulum_pendang_ss_disc6','invpendulum_pendang_ss_disc7','invpendulum_pendang_ss_disc8','-append')

save('benchmark_ss','invpendulum_cartpos_ss_disc1','invpendulum_cartpos_ss_disc2','invpendulum_cartpos_ss_disc3','invpendulum_cartpos_ss_disc4',...
    'invpendulum_cartpos_ss_disc5','invpendulum_cartpos_ss_disc6','invpendulum_cartpos_ss_disc7','invpendulum_cartpos_ss_disc8','-append')