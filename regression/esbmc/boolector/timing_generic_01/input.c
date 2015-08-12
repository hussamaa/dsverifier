#include "../../../../bmc/dsverifier.h"

digital_system ds = {
        .a = { 1.0, 1.0, 0.31, 0.03 },       
        .a_size = 4,
        .b = { 1.0, 6.0, 1.0, 6.0 },
        .b_size = 4,
	.sample_time = 0.002
};

implementation impl = {
        .int_bits = 15,
        .frac_bits = 16,
        .delta = 0.25,
        .max = 1.0,
        .min = -1.0,
        .scale = 1e6
};

hardware hw = {	
	.clock = 20000000,
        .assembly = {
		.push = 2,
		.in = 1,
		.sbiw = 2,
		.cli = 1,
		.out = 1,
		.std = 2,
		.ldd = 2,
		.subi = 1,
		.sbci = 1,
		.lsl = 1,
		.rol = 1,
		.add = 1,
		.adc = 1,
		.adiw = 2,
		.rjmp = 2,
		.mov = 1,
		.sbc = 1,
		.ld = 2,
		.rcall = 4,
		.cp = 1,
		.cpc = 1,
		.sbc = 1,
		.ldi = 1,
		.brge = 2,
		.pop = 2,
		.ret = 5,
		.st = 2,
		.brlt = 2,
		.cpi = 1   	
        }
};
