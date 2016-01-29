/*
# --------------------------------------------------
#
#  Digital-Systems Verifier (DSVerifier)
#
# --------------------------------------------------
#
#  Federal University of Amazonas - UFAM
#  Author: Hussama Ismail - hussamaismail@gmail.com
#          Iury Bessa - iury.bessa@gmail.com
#          Lucas Cordeiro - lucasccordeiro@gmail.com
#          <if you help us, put your name here!> :)
#
# --------------------------------------------------
#
#  Usage:
#    ./dsverifier file.c or file.ss
#         --realization DFI
#         --property STABILITY
#         --x-size 10
#         --timeout 3600
#
#  Supported Properties:

#  for digital-systems in transfer function:
#     OVERFLOW, LIMIT_CYCLE, ZERO_INPUT_LIMIT_CYCLE,
#     TIMING, ERROR, STABILITY, and MINIMUM_PHASE
#
#  for digital-systems using closed-loop in transfer functions:
#     STABILITY_CLOSED_LOOP, LIMIT_CYCLE_CLOSED_LOOP,
#     and QUANTIZATION_ERROR_CLOSED_LOOP
#
#  Supported Realizations:
#     DFI, DFII, TDFII,
#     DDFI, DDFII, TDDFII
#
# --------------------------------------------------
*/

#define DSVERIFIER_VERSION "2.0"

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
#include <iomanip>

typedef bool _Bool;

void __DSVERIFIER_assume(_Bool expression){
	/* nothing to do */
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
#include <Eigen/Eigenvalues>
#include <unsupported/Eigen/Polynomials>
typedef Eigen::PolynomialSolver<double, Eigen::Dynamic>::RootType RootType;
typedef Eigen::PolynomialSolver<double, Eigen::Dynamic>::RootsType RootsType;

#include <fstream>
#include <boost/algorithm/string.hpp>

const char * properties [] = { "OVERFLOW", "LIMIT_CYCLE", "ZERO_INPUT_LIMIT_CYCLE", "ERROR", "TIMING", "STABILITY", "STABILITY_CLOSED_LOOP", "LIMIT_CYCLE_CLOSED_LOOP", "QUANTIZATION_ERROR_CLOSED_LOOP" "MINIMUM_PHASE", "QUANTISATION_ERROR", "CONTROLLABILITY", "OBSERVABILITY"};
const char * realizations [] = { "DFI", "DFII", "TDFII", "DDFI", "DDFII", "TDDFII" };
const char * bmcs [] = { "ESBMC", "CBMC" };
const char * connections_mode [] = { "SERIES", "FEEDBACK" };

/* expected parameters */
unsigned int desired_x_size = 0;
std::string desired_filename;
std::string desired_property;
std::string desired_realization;
std::string desired_connection_mode;
std::string desired_timeout;
std::string desired_bmc;
std::string desired_solver;
std::string desired_macro_parameters;
std::string desired_ds_id;

/* state space */
bool stateSpaceVerification = false;
bool closedloop = false;
digital_system_state_space _controller;
double desired_quantisation_limit = 0.0;

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
	std::cout << "--realization <r>            set the realization for the Digital-System" << std::endl;
	std::cout << "                             (for Digital-Systems: DFI, DFII, TDFII, DDFI, DDFII, and TDDFII)" << std::endl;
	std::cout << "                             (for Digital-Systems in Closed-loop: DFI, DFII, and TDFII)" << std::endl;
	std::cout << "--property <p>               set the property to check in order to find violations" << std::endl;
	std::cout << "                             (for Digital-Systems: OVERFLOW, LIMIT_CYCLE, ZERO_INPUT_LIMIT_CYCLE, ERROR, TIMING, STABILITY, and MINIMUM_PHASE)" << std::endl;
	std::cout << "                             (for Digital-Systems in Closed-loop: STABILITY_CLOSED_LOOP, LIMIT_CYCLE_CLOSED_LOOP, and QUANTIZATION_ERROR_CLOSED_LOOP)" << std::endl;
	std::cout << "--x-size <k>                 set the bound of verification" << std::endl;
	std::cout << "--connection-mode <cm>       set the connection mode for the closed-loop system (SERIES or FEEDBACK)" << std::endl;
	std::cout << "--bmc <b>                    set the BMC back-end for DSVerifier (ESBMC or CBMC, default is ESBMC)" << std::endl;
	std::cout << "--solver <s>                 use the specified solver in BMC back-end (e.g., boolector, z3, yices, cvc4, and minisat)" << std::endl;
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

void validate_selected_connection_mode(std::string data){
	int length = (sizeof(connections_mode)/sizeof(*connections_mode));
	for(int i=0; i<length; i++){
		if (connections_mode[i] == data){
			desired_connection_mode = data;
			break;
		}
	}
	if (desired_connection_mode.size() == 0){
		std::cout << "invalid connection-mode: " << data << std::endl;
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
	if (file == "--help" || file == "-h") {
		help();
	} else if(file.substr(file.size()-3, std::string::npos) != ".ss"){
		std::string::size_type loc = file.find(".c", 0 );
		if( loc == std::string::npos ) {
			std::cout << file << ": failed to figure out type of file" << std::endl;
			exit(1);
		}
	} else {
		stateSpaceVerification = true;
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
		} else if (std::string(argv[i]) == "--connection-mode") {
			if (i + 1 < argc) {
				validate_selected_connection_mode(argv[++i]);
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
		} else if (std::string(argv[i]) == "--limit") {
			if (i + 1 < argc) {
				desired_quantisation_limit = std::stod(argv[++i]);
			} else {
				show_required_argument_message(argv[i]);
			}
		} else if (std::string(argv[i]) == "--closed-loop") {
			closedloop = true;
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
	char * dsverifier_home;
  dsverifier_home = getenv("DSVERIFIER_HOME");
  if (dsverifier_home == NULL){
		std::cout << std::endl << "[ERROR] - You must set DSVERIFIER_HOME environment variable." << std::endl;
		exit(1);
	}
	std::string bmc_path = std::string(dsverifier_home) + "/bmc";
	std::string model_checker_path = std::string(dsverifier_home) + "/model-checker";
	std::string command_line;
	if (desired_bmc == "ESBMC"){
		command_line = model_checker_path + "/esbmc " + desired_filename + " --no-bounds-check --no-pointer-check --no-div-by-zero-check -DBMC=ESBMC -I " + bmc_path;
		if (desired_timeout.size() > 0){
			command_line += " --timeout " + desired_timeout;
		}
	}else if (desired_bmc == "CBMC"){
		command_line =  model_checker_path + "/cbmc " + desired_filename + " --fixedbv -DBMC=CBMC -I " + bmc_path;
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
	if (desired_connection_mode.size() > 0){
		command_line += " -DCONNECTION_MODE=" + desired_connection_mode;
	}
	if (desired_x_size > 0){
		command_line += " -DX_SIZE=" + std::to_string(desired_x_size);
	}
	command_line += desired_macro_parameters;
	return command_line;
}

std::string prepare_bmc_command_line_ss(){
	std::string command_line;
	if (desired_bmc == "ESBMC"){
		command_line = "./model-checker/esbmc input.c --no-bounds-check --no-pointer-check --no-div-by-zero-check -DBMC=ESBMC";
		if (desired_timeout.size() > 0){
			command_line += " --timeout " + desired_timeout;
		}
	}else if (desired_bmc == "CBMC"){
		command_line = "cbmc --fixedbv input.c -DBMC=CBMC";
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
		command_line += " -DK_SIZE=" + std::to_string(desired_x_size);
	}
	command_line += desired_macro_parameters;
	return command_line;
}
digital_system ds;
implementation impl;

/* print array elements */
void cplus_print_fxp_array_elements(const char * name, fxp_t * v, int n){
	printf("%s = {", name);
	int i;
	for(i=0; i < n; i++){
		printf(" %jd ", v[i]);
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

	/* check the polynomial order */
	if (coefficients_vector.size() >= 3){

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
		for(unsigned int i=0; i<solver_roots.rows(); ++i){
			roots.push_back(solver_roots[i]);
		}

	} else if (coefficients_vector.size() == 2){

		double root = - coefficients_vector.at(1) / coefficients_vector.at(0);
		roots.push_back(root);

	} else {
		/* nothing to do */
	}

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

bool check_shift_stability_margin(std::vector<RootType> roots){
	std::cout << "checking shift stability margin" << std::endl;
	bool stable = true;
	for(unsigned int i=0; i<roots.size(); i++){
		std::complex<double> eig = roots.at(i);
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

void check_stability_shift_domain_using_jury(){
	show_implementation_parameters();
	std::cout << std::endl;
	double sa_fxp[ds.a_size];
	cplus_print_array_elements("original denominator", ds.a, ds.a_size);
	fxp_t a_fxp[ds.a_size];
	fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);
	fxp_to_double_array(sa_fxp, a_fxp, ds.a_size);
	cplus_print_array_elements("quantized denominator", sa_fxp, ds.a_size);
	bool is_stable = check_stability(sa_fxp, ds.a_size);
	if (is_stable){
		show_verification_successful();
	}else{
		show_verification_failed();
	}
}

void check_minimum_phase_shift_domain_using_jury(){
	show_implementation_parameters();
	std::cout << std::endl;
	double sb_fxp[ds.b_size];
	cplus_print_array_elements("original numerator", ds.b, ds.b_size);
	fxp_t b_fxp[ds.b_size];
	fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);
	fxp_to_double_array(sb_fxp, b_fxp, ds.b_size);
	cplus_print_array_elements("quantized denominator", sb_fxp, ds.b_size);
	bool is_stable = check_stability(sb_fxp, ds.b_size);
	if (is_stable){
		show_verification_successful();
	}else{
		show_verification_failed();
	}
}

void check_stability_shift_domain_using_eigen(){
	show_implementation_parameters();
	std::cout << std::endl;
	double sa_fxp[ds.a_size];
	cplus_print_array_elements("original denominator", ds.a, ds.a_size);
	fxp_t a_fxp[ds.a_size];
	fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);
	fxp_to_double_array(sa_fxp, a_fxp, ds.a_size);
	cplus_print_array_elements("quantized denominator", sa_fxp, ds.a_size);
	std::vector<RootType> poly_roots;
	get_roots_from_polynomial(sa_fxp, ds.a_size, poly_roots);
	bool is_stable = check_shift_stability_margin(poly_roots);
	if (is_stable){
		show_verification_successful();
	}else{
		show_verification_failed();
	}
}

void check_minimum_phase_shift_domain(){
	show_implementation_parameters();
	std::cout << std::endl;
	double sb_fxp[ds.b_size];
	cplus_print_array_elements("original numerator", ds.b, ds.b_size);
	fxp_t b_fxp[ds.b_size];
	fxp_double_to_fxp_array(ds.b, b_fxp, ds.b_size);
	fxp_to_double_array(sb_fxp, b_fxp, ds.b_size);
	cplus_print_array_elements("quantized numerator", sb_fxp, ds.b_size);
	bool is_stable = check_stability(sb_fxp, ds.b_size);
	if (is_stable){
		show_verification_successful();
	}else{
		show_verification_failed();
	}
}

void check_stability_delta_domain(){
	show_implementation_parameters();
	std::cout << std::endl;
	double db[ds.b_size];
	double da[ds.a_size];
	fxp_t a_fxp[ds.a_size];
	cplus_print_array_elements("original denominator", ds.a, ds.a_size);
	fxp_double_to_fxp_array(ds.a, a_fxp, ds.a_size);
	get_delta_transfer_function_with_base(ds.b, db, ds.b_size, ds.a, da, ds.a_size, impl.delta);
	cplus_print_array_elements("delta denominator", da, ds.a_size);
	fxp_t da_fxp[ds.a_size];
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
	double da[ds.a_size];
	cplus_print_array_elements("original numerator", ds.b, ds.b_size);
	get_delta_transfer_function_with_base(ds.b, db, ds.b_size, ds.a, da, ds.a_size, impl.delta);
	cplus_print_array_elements("delta numerator", db, ds.b_size);
	fxp_t db_fxp[ds.b_size];
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

void check_state_space_stability(){

	Eigen::MatrixXd matrixA = Eigen::MatrixXd::Ones(_controller.nStates,_controller.nStates);
	int i, j;
	for(i=0; i<_controller.nStates;i++){
		for(j=0; j<_controller.nStates;j++){
			matrixA(i,j) = _controller.A[i][j]; //fxp_double_to_fxp(A[i][j]);
		}
	}

	std::complex< double > lambda;
	std::complex< double > margem(1,0);
	for(i = 0; i < (matrixA.count() / 2); i++ ){
		lambda = matrixA.eigenvalues()[i];
		//std::cout << "abs(lambda): " << std::abs(lambda) << std::endl;
		double v = std::abs(lambda);
		if( v >= 1 ){
			std::cout << "unstable" << std::endl;
			exit(0);
		}
	}
	std::cout << "stable" << std::endl;
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

void extract_data_from_ss_file(){
	std::ifstream verification_file(desired_filename);
	std::string current_line;
	getline( verification_file, current_line );

	/* getting implementation specifications */
	std::string str_bits;
	int i;
	for(i = 0; current_line[i] != '<';i++);
	i++;
	for(; current_line[i] != ','; i++)
		str_bits.push_back(current_line[i]);
	impl.int_bits = std::stoi(str_bits);
	str_bits.clear();
	i++;
	for(; current_line[i] != '>'; i++)
		str_bits.push_back(current_line[i]);
	impl.frac_bits = std::stoi(str_bits);
	str_bits.clear();

	getline( verification_file, current_line ); // states

	for(i = 0; current_line[i] != '=';i++);
		i++; i++;
		for(; current_line[i] != ';'; i++)
			str_bits.push_back(current_line[i]);
		int states = std::stoi(str_bits);
		str_bits.clear();

	getline( verification_file, current_line ); // inputs

	for(i = 0; current_line[i] != '=';i++);
		i++; i++;
		for(; current_line[i] != ';'; i++)
			str_bits.push_back(current_line[i]);
		int inputs = std::stoi(str_bits);
		str_bits.clear();

	getline( verification_file, current_line ); // outputs

	for(i = 0; current_line[i] != '=';i++);
		i++; i++;
		for(; current_line[i] != ';'; i++)
			str_bits.push_back(current_line[i]);
		int outputs = std::stoi(str_bits);
		str_bits.clear();

	/* Updating _controller */
	_controller.nStates = states;
	_controller.nInputs = inputs;
	_controller.nOutputs = outputs;

	/* initialising matrix A */

	getline( verification_file, current_line ); // matrix A
	str_bits.clear();
	for(i = 0; current_line[i] != '[';i++);
	i++;
	int lines = 0;
	int columns = 0;
	for(; current_line[i] != ']'; i++){
		if(current_line[i] != ',' && current_line[i] != ';'){
			str_bits.push_back(current_line[i]);
		} else if(current_line[i] == ';'){
			_controller.A[lines][columns] = std::stod(str_bits);
			lines++;
			columns = 0;
			str_bits.clear();
		} else {
			_controller.A[lines][columns] = std::stod(str_bits);
			columns++;
			str_bits.clear();
		}
	}
	_controller.A[lines][columns] = std::stod(str_bits);
	str_bits.clear();

	/* initialising matrix B */

	getline( verification_file, current_line ); // matrix B
	str_bits.clear();
	for(i = 0; current_line[i] != '[';i++);
	i++;
	lines = 0;
	columns = 0;
	for(; current_line[i] != ']'; i++){
		if(current_line[i] != ',' && current_line[i] != ';'){
			str_bits.push_back(current_line[i]);
		} else if(current_line[i] == ';'){
			_controller.B[lines][columns] = std::stod(str_bits);
			lines++;
			columns = 0;
			str_bits.clear();
		} else {
			_controller.B[lines][columns] = std::stod(str_bits);
			columns++;
			str_bits.clear();
		}
	}
	_controller.B[lines][columns] = std::stod(str_bits);
	str_bits.clear();

	/* initialising matrix C */

	getline( verification_file, current_line ); // matrix C
	str_bits.clear();
	for(i = 0; current_line[i] != '[';i++);
	i++;
	lines = 0;
	columns = 0;
	for(; current_line[i] != ']'; i++){
		if(current_line[i] != ',' && current_line[i] != ';'){
			str_bits.push_back(current_line[i]);
		} else if(current_line[i] == ';'){
			_controller.C[lines][columns] = std::stod(str_bits);
			lines++;
			columns = 0;
			str_bits.clear();
		} else {
			_controller.C[lines][columns] = std::stod(str_bits);
			columns++;
			str_bits.clear();
		}
	}
	_controller.C[lines][columns] = std::stod(str_bits);
	str_bits.clear();

	/* initialising matrix D */

	getline( verification_file, current_line ); // matrix D
	str_bits.clear();
	for(i = 0; current_line[i] != '[';i++);
	i++;
	lines = 0;
	columns = 0;
	for(; current_line[i] != ']'; i++){
		if(current_line[i] != ',' && current_line[i] != ';'){
			str_bits.push_back(current_line[i]);
		} else if(current_line[i] == ';'){
			_controller.D[lines][columns] = std::stod(str_bits);
			lines++;
			columns = 0;
			str_bits.clear();
		} else {
			_controller.D[lines][columns] = std::stod(str_bits);
			columns++;
			str_bits.clear();
		}
	}
	_controller.D[lines][columns] = std::stod(str_bits);
	str_bits.clear();

	/* initialising matrix Inputs */

	getline( verification_file, current_line ); // matrix inputs
	str_bits.clear();
	for(i = 0; current_line[i] != '[';i++);
	i++;
	lines = 0;
	columns = 0;
	for(; current_line[i] != ']'; i++){
		if(current_line[i] != ',' && current_line[i] != ';'){
			str_bits.push_back(current_line[i]);
		} else if(current_line[i] == ';'){
			_controller.inputs[lines][columns] = std::stod(str_bits);
			lines++;
			columns = 0;
			str_bits.clear();
		} else {
			_controller.inputs[lines][columns] = std::stod(str_bits);
			columns++;
			str_bits.clear();
		}
	}
	_controller.inputs[lines][columns] = std::stod(str_bits);
	str_bits.clear();

	if(closedloop){
		getline( verification_file, current_line ); // matrix controller
		str_bits.clear();
		for(i = 0; current_line[i] != '[';i++);
		i++;
		lines = 0;
		columns = 0;
		for(; current_line[i] != ']'; i++){
			if(current_line[i] != ',' && current_line[i] != ';'){
				str_bits.push_back(current_line[i]);
			} else if(current_line[i] == ';'){
				_controller.K[lines][columns] = std::stod(str_bits);
				lines++;
				columns = 0;
				str_bits.clear();
			} else {
				_controller.K[lines][columns] = std::stod(str_bits);
				columns++;
				str_bits.clear();
			}
		}
		_controller.K[lines][columns] = std::stod(str_bits);
	}

	//print_matrix(_controller.K,1,states);
	//print_matrix(_controller.B,states,inputs);
	//print_matrix(_controller.C,outputs,states);
	//print_matrix(_controller.D,outputs,inputs);
}

void state_space_parser(){
	std::string verification_file;

	std::string tmp;
	std::ostringstream cf_value_precision;
	unsigned int i, j;
	cf_value_precision.precision(64);

	verification_file = "#include \"bmc/dsverifier.h\"\n digital_system_state_space _controller;\n implementation impl = {\n .int_bits = ";
	verification_file.append(std::to_string(impl.int_bits));
	verification_file.append(",\n .frac_bits = ");
	verification_file.append(std::to_string(impl.frac_bits));
	verification_file.append("};\n int nStates = ");
	verification_file.append(std::to_string(_controller.nStates));
	verification_file.append(";\n int nInputs = ");
	verification_file.append(std::to_string(_controller.nInputs));
	verification_file.append(";\n int nOutputs = ");
	verification_file.append(std::to_string(_controller.nOutputs));
	verification_file.append(";\n double error_limit = ");
	cf_value_precision  << std::fixed << desired_quantisation_limit;
	verification_file.append(cf_value_precision.str());
	verification_file.append(";\n void initials(){\n");

	for (i=0; i<_controller.nStates; i++) {
		for (j=0; j<_controller.nStates; j++) {
			verification_file.append("\t_controller.A[");
			verification_file.append(std::to_string(i));
			verification_file.append("][");
			verification_file.append(std::to_string(j));
			verification_file.append("] = ");
			cf_value_precision.str(std::string());
			cf_value_precision << std::fixed << _controller.A[i][j];
			verification_file.append(cf_value_precision.str());
			verification_file.append(";\n");
		}
	}

	for (i=0; i<_controller.nStates; i++) {
		for (j=0; j<_controller.nInputs; j++) {
			verification_file.append("\t_controller.B[");
			verification_file.append(std::to_string(i));
			verification_file.append("][");
			verification_file.append(std::to_string(j));
			verification_file.append("] = ");
			cf_value_precision.str(std::string());
			cf_value_precision << std::fixed << _controller.B[i][j];
			verification_file.append(cf_value_precision.str());
			verification_file.append(";\n");
		}
	}

	for (i=0; i<_controller.nOutputs; i++) {
		for (j=0; j<_controller.nStates; j++) {
			verification_file.append("\t_controller.C[");
			verification_file.append(std::to_string(i));
			verification_file.append("][");
			verification_file.append(std::to_string(j));
			verification_file.append("] = ");
			cf_value_precision.str(std::string());
			cf_value_precision << std::fixed << _controller.C[i][j];
			verification_file.append(cf_value_precision.str());
			verification_file.append(";\n");
		}
	}

	for (i=0; i<_controller.nOutputs; i++) {
		for (j=0; j<_controller.nInputs; j++) {
			verification_file.append("\t_controller.D[");
			verification_file.append(std::to_string(i));
			verification_file.append("][");
			verification_file.append(std::to_string(j));
			verification_file.append("] = ");
			cf_value_precision.str(std::string());
			cf_value_precision << std::fixed << _controller.D[i][j];
			verification_file.append(cf_value_precision.str());
			verification_file.append(";\n");
		}
	}

	for (i=0; i<_controller.nInputs; i++) {
		for (j=0; j < 1; j++) {
			verification_file.append("\t_controller.inputs[");
			verification_file.append(std::to_string(i));
			verification_file.append("][");
			verification_file.append(std::to_string(j));
			verification_file.append("] = ");
			cf_value_precision.str(std::string());
			cf_value_precision << std::fixed << _controller.inputs[i][j];
			verification_file.append(cf_value_precision.str());
			verification_file.append(";\n");
		}
	}

	verification_file.append("}");

	std::ofstream myfile ("input.c");
	if (myfile.is_open())
	{
		myfile << verification_file;
		myfile.close();
	}
	else std::cout << "Unable to open file";
}

void closed_loop(){

	double result1[LIMIT][LIMIT];

	int i, j, k;
	for(i=0; i<LIMIT;i++)
		for(j=0; j<LIMIT;j++)
			result1[i][j]=0;

	double_matrix_multiplication(_controller.nStates,_controller.nInputs,1,_controller.nStates,_controller.B,_controller.K,result1);

	double_sub_matrix(_controller.nStates,
			_controller.nStates,
			_controller.A,
			result1,
			_controller.A);

	for(i=0; i<LIMIT;i++)
		for(j=0; j<LIMIT;j++)
			result1[i][j]=0;

	double_matrix_multiplication(_controller.nOutputs,_controller.nInputs,1,_controller.nStates,_controller.D,_controller.K,result1);

	double_sub_matrix(_controller.nOutputs,
			_controller.nStates,
			_controller.C,
			result1,
			_controller.C);
}

/* main function */
int main(int argc, char* argv[]){

	/* without overflow */
	OVERFLOW_MODE = NONE;

	bind_parameters(argc, argv);

	if(desired_property == "QUANTISATION_ERROR" && desired_quantisation_limit == 0.0)
		show_required_argument_message("QUANTISATION_ERROR");

	check_file_exists();

	std::cout << "Running: Digital Systems Verifier (DSVerifier)" << std::endl;

	if (stateSpaceVerification){
		extract_data_from_ss_file();
		if(closedloop)
			closed_loop();
		if( desired_property == "STABILITY" ){
			std::cout << "Checking stability..." << std::endl;
			check_state_space_stability();
			exit(0);
		} else if( desired_property == "QUANTISATION_ERROR" ) {
			state_space_parser();
			std::string command_line = prepare_bmc_command_line_ss();
			std::cout << "Back-end Verification: " << command_line << std::endl;
			execute_command_line(command_line);
			exit(0);
		} else if( desired_property == "CONTROLLABILITY" ) {
			state_space_parser();
			std::string command_line = prepare_bmc_command_line_ss();
			std::cout << "Back-end Verification: " << command_line << std::endl;
			execute_command_line(command_line);
			exit(0);
		} else if( desired_property == "OBSERVABILITY" ) {
			state_space_parser();
			std::string command_line = prepare_bmc_command_line_ss();
			std::cout << "Back-end Verification: " << command_line << std::endl;
			execute_command_line(command_line);
			exit(0);
		} else {
			std::cout << "Nothing to check!" << std::endl;
		}
	} else {
		bool is_restricted_property = (desired_property == "STABILITY" || desired_property == "MINIMUM_PHASE");
		bool is_delta_realization = (desired_realization == "DDFI" || desired_realization == "DDFII" || desired_realization == "TDDFII");

		if (!(is_restricted_property)){
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
				} else if ((desired_property == "STABILITY")){
					check_stability_shift_domain_using_jury();
					exit(0);
				} else if ((desired_property == "MINIMUM_PHASE")){
					check_minimum_phase_shift_domain_using_jury();
					exit(0);
				}
			}catch(std::exception & e){
				std::cout << std::endl << "[INTERNAL ERROR] - An unexpected event occurred " << std::endl;
			}
		}
	}
}
