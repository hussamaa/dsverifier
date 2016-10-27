function verify_cl_quantization_error(system, bmc, realization, xsize, c_mode, error, varargin)

global property;

%setting the DSVERIFIER_HOME
dsv_setup();

%translate to ANSI-C file
dsv_parser(system,'cl', error);

%verifying using DSVerifier command-line
property = 'QUANTIZATION_ERROR_CLOSED_LOOP';

extra_param = get_macro_params(nargin-1,varargin,'cl');

command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc  ' --connection-mode ' c_mode extra_param];
dsv_verification(command_line,'cl');

%report the verification
output = dsv_report('output.out','cl');
disp(output);

end

