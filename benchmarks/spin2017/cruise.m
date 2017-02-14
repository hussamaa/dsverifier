%%%%%%%%%%
% 
% Cruise Control
% 
% Extracted from:
%   Feedback Control of Dynamics Systems, 6th ed
%   Franklin, G. F.; Powell, J. D.; Emami-Naemi
% Written by:
%   Iury Bessa
%   Manaus, 2016
%%%%%%%%%%
%%

m=1000;
b=50;

num=[1/m];
den=[1,b/m];

cruise_tf_cont=tf(num,den);


%% Discretizing with Ts=1

ts=1;
cruise_tf_disc1=c2d(cruise_tf_cont,ts);
cruise_ss_disc1=ss(cruise_tf_disc1);

%% Discretizing with Ts=1.5

ts=1.5;
cruise_tf_disc2=c2d(cruise_tf_cont,ts);
cruise_ss_disc2=ss(cruise_tf_disc2);

%% Discretizing with Ts=0.5

ts=0.5;
cruise_tf_disc3=c2d(cruise_tf_cont,ts);
cruise_ss_disc3=ss(cruise_tf_disc3);

%% Discretizing with Ts=0.2

ts=0.2;
cruise_tf_disc4=c2d(cruise_tf_cont,ts);
cruise_ss_disc4=ss(cruise_tf_disc4);

%% Discretizing with Ts=0.1

ts=0.1;
cruise_tf_disc5=c2d(cruise_tf_cont,ts);
cruise_ss_disc5=ss(cruise_tf_disc5);

%% Discretizing with Ts=0.05

ts=0.05;
cruise_tf_disc6=c2d(cruise_tf_cont,ts);
cruise_ss_disc6=ss(cruise_tf_disc6);

%% Discretizing with Ts=0.01

ts=0.01;
cruise_tf_disc7=c2d(cruise_tf_cont,ts);
cruise_ss_disc7=ss(cruise_tf_disc7);

%% Saving

save('benchmark_tf','cruise_tf_disc1','cruise_tf_disc2','cruise_tf_disc3','cruise_tf_disc4',...
    'cruise_tf_disc5','cruise_tf_disc6','cruise_tf_disc7','-append')

save('benchmark_ss','cruise_ss_disc1','cruise_ss_disc2','cruise_ss_disc3','cruise_ss_disc4',...
    'cruise_ss_disc5','cruise_ss_disc6','cruise_ss_disc7','-append')