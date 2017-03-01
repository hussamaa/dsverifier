%%%%%%%%%%
% 
% USCG cutter Tampa Heading Angle
% 
% Extracted from:
%   Feedback Control of Dynamics Systems, 6th ed
%   Franklin, G. F.; Powell, J. D.; Emami-Naemi
% Written by:
%   Iury Bessa
%   Manaus, 2016
%%%%%%%%%%
%%


uscgtampa_tf_cont=tf(zpk([-0.0068],[0,-0.2647,-0.0063],-0.0184));

%% Discretizing with Ts=1

ts=1;
uscgtampa_tf_disc1=c2d(uscgtampa_tf_cont,ts);
uscgtampa_ss_disc1=ss(uscgtampa_tf_disc1);

%% Discretizing with Ts=1.5

ts=1.5;
uscgtampa_tf_disc2=c2d(uscgtampa_tf_cont,ts);
uscgtampa_ss_disc2=ss(uscgtampa_tf_disc2);

%% Discretizing with Ts=0.5

ts=0.5;
uscgtampa_tf_disc3=c2d(uscgtampa_tf_cont,ts);
uscgtampa_ss_disc3=ss(uscgtampa_tf_disc3);

%% Discretizing with Ts=0.2

ts=0.2;
uscgtampa_tf_disc4=c2d(uscgtampa_tf_cont,ts);
uscgtampa_ss_disc4=ss(uscgtampa_tf_disc4);

%% Discretizing with Ts=0.1

ts=0.1;
uscgtampa_tf_disc5=c2d(uscgtampa_tf_cont,ts);
uscgtampa_ss_disc5=ss(uscgtampa_tf_disc5);

%% Discretizing with Ts=0.05

ts=0.05;
uscgtampa_tf_disc6=c2d(uscgtampa_tf_cont,ts);
uscgtampa_ss_disc6=ss(uscgtampa_tf_disc6);

%% Discretizing with Ts=0.01

ts=0.01;
uscgtampa_tf_disc7=c2d(uscgtampa_tf_cont,ts);
uscgtampa_ss_disc7=ss(uscgtampa_tf_disc7);

%% Discretizing with Ts=0.005

ts=0.005;
uscgtampa_tf_disc8=c2d(uscgtampa_tf_cont,ts);
uscgtampa_ss_disc8=ss(uscgtampa_tf_disc8);


%% Saving

save('benchmark_tf','uscgtampa_tf_disc1','uscgtampa_tf_disc2','uscgtampa_tf_disc3','uscgtampa_tf_disc4',...
    'uscgtampa_tf_disc5','uscgtampa_tf_disc6','uscgtampa_tf_disc7','uscgtampa_tf_disc8','-append')
save('benchmark_ss','uscgtampa_ss_disc1','uscgtampa_ss_disc2','uscgtampa_ss_disc3','uscgtampa_ss_disc4',...
    'uscgtampa_ss_disc5','uscgtampa_ss_disc6','uscgtampa_ss_disc7','uscgtampa_ss_disc8','-append')