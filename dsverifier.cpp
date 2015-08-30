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
#include <complex>
#include <algorithm>
#include <cmath>
#include <exception>
#include <assert.h>

typedef bool _Bool;

void __DSVERIFIER_assume(_Bool expression){
	/* do nothing */
}

void __DSVERIFIER_assert(_Bool expression){
	if (expression == 0){
		 throw 0;
	}
}

#include "bmc/core/definitions.h"
#include "bmc/core/fixed-point.h"
#include "bmc/core/util.h"
#include "bmc/core/delta-operator.h"
#include "bmc/core/initialization.h"

/* eigen dependencies */
#include <unsupported/Eigen/Polynomials>
typedef Eigen::PolynomialSolver<double, Eigen::Dynamic>::RootType RootType;
typedef Eigen::PolynomialSolver<double, Eigen::Dynamic>::RootsType RootsType;

#include <fstream>
#include <boost/algorithm/string.hpp>

#define DSVERIFIER_VERSION 1.2

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
std::string desired_ds_id;

void help () {
	std::cout << std::endl;
	std::cout << "* * *           DSVerifier " << DSVERIFIER_VERSION << "          * * *" << std::endl;
	std::cout << "" << std::endl;
	std::cout << "Usage:                       Purpose:" << std::endl;
	std::cout << "" << std::endl;
	std::cout << "dsverifier [-h] [--help]           show help" << std::endl;
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
				/* check if there is an desired benchmark */
				std::string::size_type find_desired_ds_id = parameter.find("-DDS_ID=", 0 );
				if( find_desired_ds_id != std::string::npos ) {
					std::vector<std::string> parts;
					boost::split(parts, parameter, boost::is_any_of("="));
					desired_ds_id = "DS_ID==" + parts.at(1);
				}
			}else{
				std::cout << "invalid parameter: " << argv[i] << std::endl;
				exit(1);
			}
		}
	}
	check_required_parameters();
}

std::string execute_command_line(std::string command){
	FILE* pipe = popen(command.c_str(), "r");
	if (!pipe) return "ERROR";
	char buffer[128];
	std::string result = "";
	while(!feof(pipe)) {
		if(fgets(buffer, 128, pipe) != NULL){
			std::cout << buffer;
			result += buffer;
		}
	}
	pclose(pipe);
	return result;
}

std::string prepare_bmc_command_line(){
	std::string command_line;
	if (desired_bmc == "ESBMC"){
		command_line = "esbmc " + desired_filename + " --no-bounds-check --no-pointer-check --no-div-by-zero-check -DBMC=ESBMC";
		if (desired_timeout.size() > 0){
			command_line += " --timeout " + desired_timeout;
		}
	}else if (desired_bmc == "CBMC"){
		command_line = "cbmc --fixedbv " + desired_filename + " -DBMC=CBMC";
	}
	if (desired_solver.size() > 0){
		command_line += " --" + desired_solver;
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

digital_system ds;
implementation impl;

/* print array elements */
void cplus_print_fxp_array_elements(const char * name, fxp32_t * v, int n){
   printf("%s = {", name);
   int i;
   for(i=0; i < n; i++){
      printf(" %d ", v[i]);
   }
   printf("}\n");
}

/* print array elements */
void cplus_print_array_elements(const char * name, double * v, int n){
   printf("%s = {", name);
   int i;
   for(i=0; i < n; i++){
      printf(" %.32f ", v[i]);
   }
   printf("}\n");
}

int get_roots_from_polynomial(double polynomial[], int poly_size, std::vector<RootType> & roots){

	unsigned int size = poly_size;

	/* coefficients */
	std::vector<double> coefficients_vector;
	for (int i=0; i< poly_size; i++){
		coefficients_vector.push_back(polynomial[i]);
	}

	/* remove leading zeros */
	std::vector<double>::iterator it=coefficients_vector.begin();
	while(it != coefficients_vector.end()){
		if(*it != 0.0)
			break;
		it=coefficients_vector.erase(it);
	}

	size=coefficients_vector.size();

	/* check if there is any element left on the vector */
	if(!size){
		std::cout << std::endl << "No remaining elements in polynomial vector";
		throw std::runtime_error ("tla");
	}

	Eigen::VectorXd coefficients(coefficients_vector.size());

	/* copy elements from the list to the array - insert in reverse order */
	unsigned int i=0;
	for(it=coefficients_vector.begin();
			it!=coefficients_vector.end();
			++it, ++i){
		coefficients[size-i-1] = *it;
	}

	/* eigen solver object */
	Eigen::PolynomialSolver<double, Eigen::Dynamic> solver;

	/* solve denominator using QR decomposition */
	solver.compute(coefficients);

	RootsType solver_roots = solver.roots();
	for(unsigned int i=0; i<solver_roots.rows(); ++i)
	roots.push_back(solver_roots[i]);

	return 0;
}

bool check_delta_stability_margin(std::vector<RootType> roots){
	std::cout << "checking delta stability margin" << std::endl;
	bool stable = true;
	for(unsigned int i=0; i<roots.size(); i++){
		std::complex<double> eig = roots.at(i);
		eig.real(eig.real() * impl.delta);
		eig.imag(eig.imag() * impl.delta);
		eig.real(eig.real() + 1);
		if ((std::abs(eig) < 1) == false){
			stable = false;
			break;
		}
	}
	return stable;
}

void show_delta_not_representable(){
	std::cout << "[EXCEPTION] Does not possible to represent this value in delta using this precision" << std::endl;
}

void show_verification_successful(){
	std::cout << std::endl << "VERIFICATION SUCCESSFUL" << std::endl;
}

void show_verification_failed(){
	std::cout << std::endl << "VERIFICATION FAILED" << std::endl;
}

void show_implementation_parameters(){
	std::cout << std::endl << "implementation int_bits: " << impl.int_bits << std::endl;
	std::cout << "implementation frac_bits: " << impl.frac_bits << std::endl;
	std::cout << "implementation delta: " << impl.delta << std::endl;
}

void check_stability_delta_domain(){
	show_implementation_parameters();
	std::cout << std::endl;
	double da[ds.a_size];
	cplus_print_array_elements("original denominator", ds.a, ds.a_size);
	generate_delta_coefficients(ds.a, da, ds.a_size, impl.delta);
	cplus_print_array_elements("delta denominator", da, ds.a_size);
	fxp32_t da_fxp[ds.a_size];
	try{
		fxp_double_to_fxp_array(da, da_fxp, ds.a_size);
	} catch (int e){
		std::cout << "an fixed-point arithmetic overflow occurs after delta transformation" << std::endl;
		show_verification_failed();
		exit(1);
	}
	if ((da[0] != 0) && (da_fxp[0] == 0)){
		std::cout << std::endl;
		std::cout << "ds.a[0] = "<< std::to_string(da[0]) << " ----> " << std::to_string(da_fxp[0]) << std::endl;
		show_delta_not_representable();
		exit(1);
	}
	double da_qtz[ds.a_size];
	fxp_to_double_array(da_qtz, da_fxp, ds.a_size);
	cplus_print_array_elements("quantized delta denominator", da_qtz, ds.a_size);
	std::vector<RootType> poly_roots;
	get_roots_from_polynomial(da_qtz, ds.a_size, poly_roots);
	bool is_stable = check_delta_stability_margin(poly_roots);
	if (is_stable){
		show_verification_successful();
	}else{
		show_verification_failed();
	}
}

bool check_if_file_exists (const std::string & name) {
    if (FILE *file = fopen(name.c_str(), "r")) {
        fclose(file);
        return true;
    } else {
        return false;
    }
}

void check_minimum_phase_delta_domain(){
	show_implementation_parameters();
	std::cout << std::endl;
	double db[ds.b_size];
	cplus_print_array_elements("original numerator", ds.b, ds.b_size);
	generate_delta_coefficients(ds.b, db, ds.b_size, impl.delta);
	cplus_print_array_elements("delta numerator", db, ds.b_size);
	fxp32_t db_fxp[ds.b_size];
	fxp_double_to_fxp_array(db, db_fxp, ds.b_size);
	if ((db[0] != 0) && (db_fxp[0] == 0)){
		std::cout << std::endl;
		std::cout << "ds.b[0] = "<< std::to_string(db[0]) << " ----> " << std::to_string(db_fxp[0]) << std::endl;
		show_delta_not_representable();
		exit(1);
	}
	double db_qtz[ds.b_size];
	fxp_to_double_array(db_qtz, db_fxp, ds.b_size);
	cplus_print_array_elements("quantized delta numerator", db_qtz, ds.b_size);
	std::vector<RootType> poly_roots;
	get_roots_from_polynomial(db_qtz, ds.b_size, poly_roots);
	bool is_stable = check_delta_stability_margin(poly_roots);
	if (is_stable){
		show_verification_successful();
	}else{
		show_verification_failed();
	}
}

void check_file_exists(){
	/* check if the specified file exists */
	if (check_if_file_exists(desired_filename) == false){
		std::cout << "file " << desired_filename << ": failed to open input file" << std::endl;
		exit(1);
	}
}

std::string replace_all_string(std::string str, const std::string& from, const std::string& to) {
    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length(); // Handles case where 'to' is a substring of 'from'
    }
    return str;
}

void extract_data_from_file(){

	std::ifstream verification_file(desired_filename);
	int readed_attributes = 0;
	int expected_attributes = 5;
	bool ds_id_found = false;

	for(std::string current_line; getline( verification_file, current_line );){

		/* removing whitespaces */
		current_line = replace_all_string(current_line, " ", "");
		current_line = replace_all_string(current_line, "\t", "");
		/* check the last comma, and remove it */
		if (current_line.back() == ','){
			current_line.pop_back();
		}

		/* check if there is an desired ds_id and find the region*/
		if (desired_ds_id.size() != 0){
			std::string::size_type find_desired_ds_id = current_line.find(desired_ds_id, 0);
			if (ds_id_found == false){
				if (find_desired_ds_id != std::string::npos){
					ds_id_found = true;
				} else {
					continue; /* go to next line */
				}
			}
		}

		/* check if all expected attributes were found */
		if (readed_attributes == expected_attributes){
			break;
		}

		std::string::size_type ds_a = current_line.find(".a=", 0);
		if (ds_a != std::string::npos){
			std::vector<std::string> coefficients;
			boost::split(coefficients, current_line, boost::is_any_of(","));
			for(int i=0; i< coefficients.size(); i++){
				std::string coefficient = coefficients.at(i);
				coefficient = replace_all_string(coefficient, ".a={", "");
				coefficient = replace_all_string(coefficient, "}", "");
				ds.a[i] = std::atof(coefficient.c_str());
				ds.a_size = coefficients.size();
			}
			readed_attributes++;
			continue;
		}
		std::string::size_type ds_b = current_line.find(".b=", 0);
		if (ds_b != std::string::npos){
			std::vector<std::string> coefficients;
			boost::split(coefficients, current_line, boost::is_any_of(","));
			for(int i=0; i< coefficients.size(); i++){
				std::string coefficient = coefficients.at(i);
				coefficient = replace_all_string(coefficient, ".b={", "");
				coefficient = replace_all_string(coefficient, "}", "");
				ds.b[i] = std::atof(coefficient.c_str());
				ds.b_size = coefficients.size();
			}
			readed_attributes++;
			continue;
		}
		std::string::size_type impl_int_bits = current_line.find(".int_bits", 0);
		if (impl_int_bits != std::string::npos){
			current_line = replace_all_string(current_line, ".int_bits=", "");
			impl.int_bits = std::atoi(current_line.c_str());
			readed_attributes++;
			continue;
		}
		std::string::size_type impl_frac_bits = current_line.find(".frac_bits", 0);
		if (impl_frac_bits != std::string::npos){
			current_line = replace_all_string(current_line, ".frac_bits=", "");
			impl.frac_bits = std::atoi(current_line.c_str());
			readed_attributes++;
			continue;
		}
		std::string::size_type impl_delta = current_line.find(".delta", 0);
		if (impl_delta != std::string::npos){
			current_line = replace_all_string(current_line, ".delta=", "");
			impl.delta = std::atof(current_line.c_str());
			readed_attributes++;
			continue;
		}
	}

}

/* main function */
int main(int argc, char* argv[]){

	/* without overflow */
	OVERFLOW_MODE = 0;

	bind_parameters(argc, argv);

	check_file_exists();

	std::cout << "Running: Digital Systems Verifier (DSVerifier)" << std::endl;
	bool is_restricted_property = (desired_property == "STABILITY" || desired_property == "MINIMUM_PHASE");
	bool is_delta_realization = (desired_realization == "DDFI" || desired_realization == "DDFII" || desired_realization == "TDDFII");

	if (!(is_restricted_property && is_delta_realization)){

		/* normal flow using bmc */
		std::string command_line = prepare_bmc_command_line();
		std::cout << "Back-end Verification: " << command_line << std::endl;
		execute_command_line(command_line);
		exit(0);

	}else{
		try{
			extract_data_from_file();
			initialization();
			if ((is_delta_realization == true) && desired_property == "STABILITY"){
				check_stability_delta_domain();
				exit(0);
			} else if ((is_delta_realization == true) && desired_property == "MINIMUM_PHASE"){
				check_minimum_phase_delta_domain();
				exit(0);
			}
		}catch(std::exception & e){
			std::cout << std::endl << "[INTERNAL ERROR] - An unexpected event occurred " << std::endl;
		}
	}
}
