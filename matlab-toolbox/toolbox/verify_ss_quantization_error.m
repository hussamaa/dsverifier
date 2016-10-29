function verify_ss_quantization_error(system, bmc, realization, xsize, error, varargin)

global property;
%setting the DSVERIFIER_HOME
dsv_setup();
%translate to ANSI-C file
dsv_parser(system,'ss',error);
%verifying using DSVerifier command-line
property = 'QUANTISATION_ERROR';

extra_param = get_macro_params(nargin-1,varargin,'ss');

command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc extra_param];
dsv_verification(command_line,'ss');
%report the verification
output = dsv_report('output.out','ss');
disp(output);
end

