#include <iostream>
#include <stdlib.h>

#define VERSION 1.2

void help () {
	std::cout << std::endl;
	std::cout << "* * *           DSVerifier " << VERSION << "          * * *" << std::endl;
	std::cout << "" << std::endl;
	std::cout << "Usage:                       Purpose:" << std::endl;
	std::cout << "" << std::endl;
	std::cout << "dsverifier [-?] [--help]           show help" << std::endl;
	std::cout << "dsverifier file.c ...              source file names" << std::endl;
	std::cout << "" << std::endl;
	std::cout << "Options:" << std::endl;
	std::cout << "" << std::endl;

	std::cout << "--realization <r>            set the realization for the digital system" << std::endl;
	std::cout << "                             (Available: DFI, DFII, TDFII, DDFI, DDFII, TDDFII, CDFI, CDFII, CTDFII, CDDFI, CDDFII, CTDDFII)" << std::endl;
	std::cout << "--property <p>               set the property to check in order to find violations" << std::endl;
	std::cout << "                             (Available: OVERFLOW, LIMIT_CYCLE, TIMING, STABILITY, and MINIMUM_PHASE)" << std::endl;
	std::cout << "--x-size <k>                 set the bound of verification" << std::endl;
	std::cout << "--timeout <t>                set the maximum time of verification" << std::endl;
	std::cout << "" << std::endl;
	exit(0);
}

int main(){
   help();
}
