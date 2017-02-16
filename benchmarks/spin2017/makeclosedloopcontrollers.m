digital_system(1).plant=tf([0.1898, 1.8027E-4],[1.0, -0.9012, -1.0006E-16], 2); %dcmotor
digital_system(2).plant=tf([0.2039, 0.2039],[1.0, 1.19999, 1.0],2); %pendulum
digital_system(3).plant=tf([0.0200, -3.8303E-176],[1.0, -4.6764E-166],2); %tapedriver
digital_system(4).plant=tf([0.25, 0.5, 0.25, -4.3341E-7],[1.0, 5.9150E-6, 1.0480E-11, -4.9349E-63, 7.0168E-225],2); %suspension
digital_system(5).plant=tf([15.1315, 17.8600, 17.4549],[1.0, -2.6207, 2.3586, -0.6570],2); %helicopter

digital_system(1).controller=tf([0.6875, 0.03125],[0.9921875, 0.0, 0.0],2);
digital_system(2).controller=tf([0.2, -0.18], [1.0, 0.3], 2);
digital_system(3).controller=tf([0.2, -0.18],[1.0, 0.3],2);
digital_system(4).controller=tf([0.0546875],[0.126953125],2);
digital_system(5).controller=tf([0.005859375],[ 0.25, 0.125],2);

digital_system(1).rangeMax=1; digital_system(1).rangeMin=-1;
digital_system(2).rangeMax=1; digital_system(2).rangeMin=-1;
digital_system(3).rangeMax=1; digital_system(3).rangeMin=-1;
digital_system(4).rangeMax=1; digital_system(4).rangeMin=-1;
digital_system(5).rangeMax=1; digital_system(5).rangeMin=-1;

digital_system(1).int_bits=3; digital_system(1).frac_bits= 7 ;
digital_system(2).int_bits=3; digital_system(2).frac_bits= 7 ;
digital_system(3).int_bits=3; digital_system(3).frac_bits= 7 ;
digital_system(4).int_bits=3; digital_system(4).frac_bits= 7 ;
digital_system(5).int_bits=3; digital_system(5).frac_bits= 7 ;

digital_system(1).realization='DFI'
digital_system(2).realization='DFI'
digital_system(3).realization='DFI'
digital_system(4).realization='DFI'
digital_system(5).realization='DFI'
