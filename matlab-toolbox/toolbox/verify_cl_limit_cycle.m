function verify_cl_limit_cycle(system, bmc, realization, xsize, c_mode, varargin)

global property;

%setting the DSVERIFIER_HOME
dsv_setup();

%translate to ANSI-C file
dsv_parser(system,'cl',0);

%verifying using DSVerifier command-line
property = 'LIMIT_CYCLE_CLOSED_LOOP';

extra_param = get_macro_params(nargin,varargin,'cl');

command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc ' --connection-mode ' c_mode extra_param];
dsv_verification(command_line,'cl');

%report the verification
output = dsv_report('output.out','cl');
disp(output);

end

