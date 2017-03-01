% Plants
digital_system(1).plant=tf([9.7541E-04],[1.0, -0.9512], 0.2); %cruise
digital_system(2).plant=tf([0.1898, 1.8027E-4],[1.0, -0.9012, -1.0006E-16],2); %dc-motor
digital_system(3).plant=tf([0.0001929, 6.814e-09],[1.0, -0.6921, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],0.01); %dc-servo-motor
digital_system(4).plant=tf([-0.01285, 0.02582, -0.01293],[1.0, -2.99, 2.983, -0.9929],0.01); %doyleetal
digital_system(5).plant=tf([15.1315, 17.8600, 17.4549],[1.0, -2.6207, 2.3586, -0.6570],2); %helicopter 
digital_system(6).plant=tf([0.2039, 0.2039],[1.0, 1.19999, 1.0 ],2); %pendulum 
digital_system(7).plant=tf([1.250000e-1, 1.250000e-1],[1.000000, -2.000000, 1.000000],0.001); %satelliteB2 
digital_system(8).plant=tf([5.000000e-5, 5.000000e-5],[1.000000, -2.000000, 1.000000],0.001); %spgMsDamper 
digital_system(9).plant=tf([0.25, 0.5, 0.25, -4.3341E-7],[1.0, 5.9150E-6, 1.0480E-11, -4.9349E-63, 7.0168E-225],2); %suspension 
digital_system(10).plant=tf([0.0200, -3.8303E-176],[1.0, -4.6764E-166], 2); %tapedriver 


%Controllers
digital_system(1).controller=tf([0.00390625, 0.0009765625],[0.3134765625, -0.0009765625],0.2); %cruise
digital_system(2).controller=tf([-0.3466796875, 0.015625],[0.5, 0.19921875, 0], 2); %dc-motor
digital_system(3).controller=tf([0.5, -0.96875, -0.875, -0.5],[0.001190185546875, 0.0008544921875, 0.000152587890625, 0.000335693359375, 0, 0, 0, 0, 0],0.01); %dc-servo-motor
digital_system(4).controller=tf([-0.580535888671875, 0.919769287109375, 0.11871337890625, -0.951934814453125],[0.7188720703125, -0.38751220703125, -0.415924072265625, 0.437286376953125],0.01); %doyleetal
digital_system(5).controller=tf([-0.0009765625, 0, 0],[ 0.76171875, 0, 0, 0 ],2); %helicopter
digital_system(6).controller=tf([-0.96484375, 0.9833984375],[0.8896484375, -0.875, 0 ],2); %pendulum 
digital_system(7).controller=tf([0.8359375, 0.265625, -0.96875],[0.9453125, 0.90625, -0.15625, -0.123046875],0.001); %satelliteB2 
digital_system(8).controller=tf([-0.0000000004656612873077392578125, 1.0000000004656612873077392578125, -1.0000000004656612873077392578125 ],[1, -0.0000000004656612873077392578125, 0.0000000004656612873077392578125],0.001); %spgMsDamper 
digital_system(9).controller=tf([-0.0224609375, 0, 0, 0 ],[0.138671875, 0, 0, 0, 0],2); %suspension 
digital_system(10).controller=tf([ 0, 0.0625 ],[0.517578125, -0.4990234375], 2); %tapedriver 


%Implementation Parameters
digital_system(1).rangeMax=1; digital_system(1).rangeMin=-1;
digital_system(2).rangeMax=1; digital_system(2).rangeMin=-1;
digital_system(3).rangeMax=1; digital_system(3).rangeMin=-1;
digital_system(4).rangeMax=1; digital_system(4).rangeMin=-1;
digital_system(5).rangeMax=1; digital_system(5).rangeMin=-1;
digital_system(6).rangeMax=1; digital_system(6).rangeMin=-1;
digital_system(7).rangeMax=1; digital_system(7).rangeMin=-1;
digital_system(8).rangeMax=1; digital_system(8).rangeMin=-1;
digital_system(9).rangeMax=1; digital_system(9).rangeMin=-1;
digital_system(10).rangeMax=1; digital_system(10).rangeMin=-1;

digital_system(1).int_bits=3; digital_system(1).frac_bits= 7 ;
digital_system(2).int_bits=3; digital_system(2).frac_bits= 7 ;
digital_system(3).int_bits=4; digital_system(3).frac_bits= 11 ;
digital_system(4).int_bits=4; digital_system(4).frac_bits= 11 ;
digital_system(5).int_bits=3; digital_system(5).frac_bits= 7 ;
digital_system(6).int_bits=3; digital_system(6).frac_bits= 7 ;
digital_system(7).int_bits=3; digital_system(7).frac_bits= 7 ;
digital_system(8).int_bits=15; digital_system(8).frac_bits= 16 ;
digital_system(9).int_bits=3; digital_system(9).frac_bits= 7 ;
digital_system(10).int_bits=3; digital_system(10).frac_bits= 7 ;

digital_system(1).realization='DFI'
digital_system(2).realization='DFI'
digital_system(3).realization='DFI'
digital_system(4).realization='DFI'
digital_system(5).realization='DFI'
digital_system(6).realization='DFI'
digital_system(7).realization='DFI'
digital_system(8).realization='DFI'
digital_system(9).realization='DFI'
digital_system(10).realization='DFI'