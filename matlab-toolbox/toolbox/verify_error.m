function verify_error(system, bmc, realization, solver, xsize, error, varargin)

global property;
%setting the DSVERIFIER_HOME
dsv_setup();
%translate to ANSI-C file
dsv_parser(system,'tf', error);
%verifying using DSVerifier command-line
property = 'ERROR';

extra_param = get_macro_params(nargin-1,varargin,'tf');

command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc ' --solver ' solver extra_param];
dsv_verification(command_line,'tf');
%report the verification
output = dsv_report('output.out','tf');
disp(output);

end

