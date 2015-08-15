/**
 * DSVerifier - Digital Systems Verifier (Main)
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *
 * ------------------------------------------------------
 *
 * DSVerifier wrapper file for BMC's
 *
 * ------------------------------------------------------
*/

#include <iostream>
#include <stdlib.h>
#include <string>
#include <vector>
#include <cstdlib>

#define VERSION 1.2

const char * properties [] = { "OVERFLOW", "LIMIT_CYCLE", "TIMING", "STABILITY", "MINIMUM_PHASE" };
const char * realizations [] = { "DFI", "DFII", "TDFII", "DDFI", "DDFII", "TDDFII" };
const char * bmcs [] = { "ESBMC", "CBMC" };

/* expected parameters */
unsigned int desired_x_size = 0;
std::string desired_filename;
std::string desired_property;
std::string desired_realization;
std::string desired_timeout;
std::string desired_bmc;
std::string desired_solver;
std::string desired_macro_parameters;

void help () {
	std::cout << std::endl;
	std::cout << "* * *           DSVerifier " << VERSION << "          * * *" << std::endl;
	std::cout << "" << std::endl;
	std::cout << "Usage:                       Purpose:" << std::endl;
	std::cout << "" << std::endl;
	std::cout << "dsverifier [-?] [--help]           show help" << std::endl;
	std::cout << "dsverifier file.c ...              source file name" << std::endl;
	std::cout << "" << std::endl;
	std::cout << "Options:" << std::endl;
	std::cout << "" << std::endl;
	std::cout << "--realization <r>            set the realization for the digital system" << std::endl;
	std::cout << "                             (Available: DFI, DFII, TDFII, DDFI, DDFII, TDDFII, CDFI, CDFII, CTDFII, CDDFI, CDDFII, CTDDFII)" << std::endl;
	std::cout << "--property <p>               set the property to check in order to find violations" << std::endl;
	std::cout << "                             (Available: OVERFLOW, LIMIT_CYCLE, ZERO_INPUT_LIMIT_CYCLE, TIMING, STABILITY, and MINIMUM_PHASE)" << std::endl;
	std::cout << "--x-size <k>                 set the bound of verification" << std::endl;
	std::cout << "--bmc <b>                    set the BMC back-end for DSVerifier (ESBMC or CBMC, default is ESBMC)" << std::endl;
	std::cout << "--solver <s>                 use the specified solver in BMC back-end (e.g., boolector, z3, yices)" << std::endl;
	std::cout << "--timeout <t>                configure time limit, integer followed by {s,m,h} (for ESBMC only)" << std::endl;
	std::cout << "" << std::endl;
	exit(0);
}

void validate_selected_bmc(std::string data){
	int length = (sizeof(bmcs)/sizeof(*bmcs));
	for(int i=0; i<length; i++){
		if (bmcs[i] == data){
			desired_bmc = data;
			break;
		}
	}
	if (desired_bmc.size() == 0){
		std::cout << "invalid bmc: " << data << std::endl;
		exit(1);
	}
}

void validate_selected_realization(std::string data){
	int length = (sizeof(realizations)/sizeof(*realizations));
	for(int i=0; i<length; i++){
		if (realizations[i] == data){
			desired_realization = data;
			break;
		}
	}
	if (desired_realization.size() == 0){
		std::cout << "invalid realization: " << data << std::endl;
		exit(1);
	}
}

void validate_selected_property(std::string data){
	int length = (sizeof(properties)/sizeof(*properties));
	for(int i=0; i<length; i++){
		if (properties[i] == data){
			desired_property = data;
			break;
		}
	}
	if (desired_property.size() == 0){
		std::cout << "invalid property: " << data << std::endl;
		exit(1);
	}
}

void validate_filename(std::string file){
	std::string::size_type loc = file.find(".c", 0 );
	if( loc == std::string::npos ) {
		std::cout << file << ": failed to figure out type of file" << std::endl;
		exit(1);
	}
	desired_filename = file;
}

void show_required_argument_message(std::string parameter){
	std::cerr << parameter << " option requires one argument." << std::endl;
	exit(1);
}

void check_required_parameters(){
	if (desired_bmc.size() == 0){
		desired_bmc = "ESBMC";
	}
}

void bind_parameters(int argc, char* argv[]){
	if (argc == 1) {
		help();
		exit(1);
	}
	validate_filename(argv[1]);
	for (int i = 2; i < argc; ++i) {
		if (std::string(argv[i]) == "--help" || std::string(argv[i]) == "-h") {
			help();
		} else if (std::string(argv[i]) == "--realization") {
			if (i + 1 < argc) {
				validate_selected_realization(argv[++i]);
			} else {
				show_required_argument_message(argv[i]);
			}
		} else if (std::string(argv[i]) == "--property") {
			if (i + 1 < argc) {
				validate_selected_property(argv[++i]);
			} else {
				show_required_argument_message(argv[i]);
			}
		} else if (std::string(argv[i]) == "--x-size") {
			if (i + 1 < argc) {
				desired_x_size = std::atoi(argv[++i]);
			} else {
				show_required_argument_message(argv[i]);
			}
		} else if (std::string(argv[i]) == "--timeout") {
			if (i + 1 < argc) {
				desired_timeout = argv[++i];
			} else {
				show_required_argument_message(argv[i]);
			}
		}else if (std::string(argv[i]) == "--bmc") {
			if (i + 1 < argc) {
				validate_selected_bmc(argv[++i]);
			} else {
				show_required_argument_message(argv[i]);
			}
		}else if (std::string(argv[i]) == "--solver") {
			if (i + 1 < argc) {
				desired_solver = argv[++i];
			} else {
				show_required_argument_message(argv[i]);
			}
		} else {
			/* get macro parameters */
			std::string parameter = argv[i];
			std::string::size_type loc = parameter.find("-D", 0 );
			if( loc != std::string::npos ) {
				desired_macro_parameters += " " + parameter;
			}else{
				std::cout << "invalid parameter: " << argv[i] << std::endl;
				exit(1);
			}
		}
	}
	check_required_parameters();
}

std::string prepare_bmc_command_line(){
	std::string command_line;
	if (desired_bmc == "ESBMC"){
		command_line = "esbmc " + desired_filename + " --no-bounds-check --no-pointer-check --no-div-by-zero-check -DBMC=ESBMC";
		if (desired_timeout.size() > 0){
			command_line += " --timeout " + desired_timeout;
		}
	}else if (desired_bmc == "CBMC"){
		command_line = "cbmc " + desired_filename + " -DBMC=CBMC";
	}
	if (desired_solver.size() > 0){
		command_line += " " + desired_solver;
	}
	if (desired_realization.size() > 0){
		command_line += " -DREALIZATION=" + desired_realization;
	}
	if (desired_property.size() > 0){
		command_line += " -DPROPERTY=" + desired_property;
	}
	if (desired_x_size > 0){
		command_line += " -DX_SIZE=" + std::to_string(desired_x_size);
	}
	command_line += desired_macro_parameters;
	return command_line;
}

int main(int argc, char* argv[]){
	bind_parameters(argc, argv);
	std::string command_line = prepare_bmc_command_line();
	std::cout << command_line << std::endl;
}
