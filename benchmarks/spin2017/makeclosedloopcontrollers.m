% Plants
digital_system(1).plant=tf([9.7541E-04],[1.0, -0.9512], 2); %cruise
digital_system(2).plant=tf([0.1898, 1.8027E-4],[1.0, -0.9012, -1.0006E-16],2); %dc-motor
digital_system(3).plant=tf([0.0001929, 6.814e-09],[1.0, -0.6921, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],2); %dc-servo-motor
digital_system(4).plant=tf([-0.01285, 0.02582, -0.01293],[1.0, -2.99, 2.983, -0.9929],2); %doyleetal
digital_system(5).plant=tf([15.1315, 17.8600, 17.4549],[1.0, -2.6207, 2.3586, -0.6570],2); %helicopter
%Controllers
digital_system(1).controller=tf([0.00390625, 0.0009765625],[0.3134765625, -0.0009765625],2); %cruise
digital_system(2).controller=tf([-0.3466796875, 0.015625],[0.5, 0.19921875, 0], 2); %dc-motor
digital_system(3).controller=tf([0.5, -0.96875, -0.875, -0.5],[0.001190185546875, 0.0008544921875, 0.000152587890625, 0.000335693359375, 0, 0, 0, 0, 0],2); %dc-servo-motor
digital_system(4).controller=tf([0.0546875],[0.126953125],2); %doyleetal
digital_system(5).controller=tf([0.005859375],[ 0.25, 0.125],2); %helicopter
%Implementation Parameters
digital_system(1).rangeMax=1; digital_system(1).rangeMin=-1;
digital_system(2).rangeMax=1; digital_system(2).rangeMin=-1;
digital_system(3).rangeMax=1; digital_system(3).rangeMin=-1;
digital_system(4).rangeMax=1; digital_system(4).rangeMin=-1;
digital_system(5).rangeMax=1; digital_system(5).rangeMin=-1;

digital_system(1).int_bits=8; digital_system(1).frac_bits= 8 ;
digital_system(2).int_bits=8; digital_system(2).frac_bits= 8 ;
digital_system(3).int_bits=8; digital_system(3).frac_bits= 8 ;
digital_system(4).int_bits=8; digital_system(4).frac_bits= 8 ;
digital_system(5).int_bits=8; digital_system(5).frac_bits= 8 ;

digital_system(1).realization='DFI'
digital_system(2).realization='DFI'
digital_system(3).realization='DFI'
digital_system(4).realization='DFI'
digital_system(5).realization='DFI'
