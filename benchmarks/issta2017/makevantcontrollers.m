controller_vant(1).system=tf([ 1.5, -0.5 ],[ 1.0, 0.0 ],0.02);
controller_vant(2).system=tf([ 60.0, -50.0 ],[ 1.0, 0.0 ],0.02);
controller_vant(3).system=tf([ 110.0, -100.0 ],[ 1.0, 0.0 ],0.02);
controller_vant(4).system=tf([ 135.0, -260.0, 125.0 ],[ 1.0, -1.0, 0.0 ],0.02);
controller_vant(5).system=tf([ 2002.0, -4000.0, 1998.0 ],[ 1.0, 0.0, -1.0 ],0.02);
controller_vant(6).system=tf([ 0.93, -0.87 ],[ 1.0, 1.0 ],0.02);
controller_vant(7).system=tf([ 0.1, -0.09998 ],[ 1.0, -1.0 ],0.02);
controller_vant(8).system=tf([ 0.0096, -0.009 ],[ 0.02, 0.0 ],0.02);
controller_vant(9).system=tf([ 0.1, -0.1 ],[ 1.0, -1.0 ],0.02);

controller_vant(1).rangeMax=1; controller_vant(1).rangeMin=-1;
controller_vant(2).rangeMax=1; controller_vant(2).rangeMin=-1;
controller_vant(3).rangeMax=1; controller_vant(3).rangeMin=-1;
controller_vant(4).rangeMax=1; controller_vant(4).rangeMin=-1;
controller_vant(5).rangeMax=1; controller_vant(5).rangeMin=-1;
controller_vant(6).rangeMax=1; controller_vant(6).rangeMin=-1;
controller_vant(7).rangeMax=1; controller_vant(7).rangeMin=-1;
controller_vant(8).rangeMax=1; controller_vant(8).rangeMin=-1;
controller_vant(9).rangeMax=1; controller_vant(9).rangeMin=-1;

controller_vant(1).int_bits=2; controller_vant(1).frac_bits= 14 ;
controller_vant(2).int_bits=6; controller_vant(2).frac_bits= 10 ;
controller_vant(3).int_bits=7; controller_vant(3).frac_bits= 9 ;
controller_vant(4).int_bits=8; controller_vant(4).frac_bits= 8 ;
controller_vant(5).int_bits=10; controller_vant(5).frac_bits= 6 ;
controller_vant(6).int_bits=4; controller_vant(6).frac_bits= 12 ;
controller_vant(7).int_bits=4; controller_vant(7).frac_bits= 12 ;
controller_vant(8).int_bits=3; controller_vant(8).frac_bits= 13 ;
controller_vant(9).int_bits=4; controller_vant(9).frac_bits= 12 ;


controller_vant(1).realization='DFI';
controller_vant(2).realization='DFII';
controller_vant(3).realization='TDFII';
controller_vant(4).realization='DFI';
controller_vant(5).realization='DFII';
controller_vant(6).realization='TDFII';
controller_vant(7).realization='DFI';
controller_vant(8).realization='DFII';
controller_vant(9).realization='TDFII';