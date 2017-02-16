%%%%%%%%%%
% 
% Magnetic Pointer
% 
% Extracted from:
%   Feedback Control of Dynamics Systems, 6th ed
%   Franklin, G. F.; Powell, J. D.; Emami-Naemi
% Written by:
%   Iury Bessa
%   Manaus, 2016
%%%%%%%%%%
%%

I=40e-6;
k=4e-6;
Km=4e-6;
b=0.08;

num=[Km];
den=[I,b,k];
magneticpointer_tf_cont=tf(zpk([-0.0068],[0,-0.2647,-0.0063],-0.0184));

%% Discretizing with Ts=1

ts=1;
magneticpointer_tf_disc1=c2d(magneticpointer_tf_cont,ts);
magneticpointer_ss_disc1=ss(magneticpointer_tf_disc1);

%% Discretizing with Ts=1.5

ts=1.5;
magneticpointer_tf_disc2=c2d(magneticpointer_tf_cont,ts);
magneticpointer_ss_disc2=ss(magneticpointer_tf_disc2);

%% Discretizing with Ts=0.5

ts=0.5;
magneticpointer_tf_disc3=c2d(magneticpointer_tf_cont,ts);
magneticpointer_ss_disc3=ss(magneticpointer_tf_disc3);

%% Discretizing with Ts=0.2

ts=0.2;
magneticpointer_tf_disc4=c2d(magneticpointer_tf_cont,ts);
magneticpointer_ss_disc4=ss(magneticpointer_tf_disc4);

%% Discretizing with Ts=0.1

ts=0.1;
magneticpointer_tf_disc5=c2d(magneticpointer_tf_cont,ts);
magneticpointer_ss_disc5=ss(magneticpointer_tf_disc5);

%% Discretizing with Ts=0.05

ts=0.05;
magneticpointer_tf_disc6=c2d(magneticpointer_tf_cont,ts);
magneticpointer_ss_disc6=ss(magneticpointer_tf_disc6);

%% Discretizing with Ts=0.01

ts=0.01;
magneticpointer_tf_disc7=c2d(magneticpointer_tf_cont,ts);
magneticpointer_ss_disc7=ss(magneticpointer_tf_disc7);

%% Discretizing with Ts=0.005

ts=0.005;
magneticpointer_tf_disc8=c2d(magneticpointer_tf_cont,ts);
magneticpointer_ss_disc8=ss(magneticpointer_tf_disc8);


%% Saving

save('benchmark_tf','magneticpointer_tf_disc1','magneticpointer_tf_disc2','magneticpointer_tf_disc3','magneticpointer_tf_disc4',...
    'magneticpointer_tf_disc5','magneticpointer_tf_disc6','magneticpointer_tf_disc7','magneticpointer_tf_disc8','-append')
save('benchmark_ss','magneticpointer_ss_disc1','magneticpointer_ss_disc2','magneticpointer_ss_disc3','magneticpointer_ss_disc4',...
    'magneticpointer_ss_disc5','magneticpointer_ss_disc6','magneticpointer_ss_disc7','magneticpointer_ss_disc8','-append')