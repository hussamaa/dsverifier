%%%%%%%%%%
% 
% HSCC'17 Benchmarks
% 
% Written by:
%   Iury Bessa
%   Manaus, 2016
%%%%%%%%%%

%% Satellite benchmarks

satellite_tf_disc1=tf([0.5,0.5],[1,-2,1],1);
satellite_tf_disc2=tf([0.125,0.125],[1,-2,1],1);
satellite_tf_disc3=tf([2,2],[1,-2,1],2);
satellite_ss_disc1=tf([0.5,0.5],[1,-2,1],1);
satellite_ss_disc2=tf([0.125,0.125],[1,-2,1],1);
satellite_ss_disc3=tf([2,2],[1,-2,1],2);


%% Ball Magnetic Levitation

ts=001;
ballmaglev_ss_disc1=ss([1.001,0.001,-1.686e-5;1.867,1.001,-0.03349;0,0,0.9585],[-1.2e-8,3.587e-5,0.002083]',[1,0,0],[0],0.001);
ballmaglev_tf_disc1=tf(ballmaglev_ss_disc1);

%% Cruise control and Spring-mass damper

% Extracted from T. E. Wang, P. Garoche, P. Roux, R. Jobredeaux, and E. 
% Feron. Formal analysis of robustness at model and code level. 
% In Proceedings of the 19th International Conference on Hybrid Systems: 
% Computation and Control, HSCC, pages 125–134, 2016.

cruiseHSCC_tf_disc1=tf([0.0264],[1,-0.998],0.1);
springmassdamperHSCC_tf_disc1=tf([5e-5,5e-5],[1,-2,1.001],0.1);
cruiseHSCC_ss_disc1=ss(cruiseHSCC_tf_disc1);
springmassdamperHSCC_ss_disc1=ss(springmassdamperHSCC_tf_disc1);


%% Saving

save('benchmark_tf','satellite_tf_disc1','satellite_tf_disc2','satellite_tf_disc3','ballmaglev_tf_disc1',...
    'cruiseHSCC_tf_disc1','springmassdamperHSCC_tf_disc1','-append')
save('benchmark_ss','satellite_ss_disc1','satellite_ss_disc2','satellite_ss_disc3','ballmaglev_ss_disc1',...
    'cruiseHSCC_ss_disc1','springmassdamperHSCC_ss_disc1','-append')