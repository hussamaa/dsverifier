function verify_cl_quantization_error(system, bmc, realization, solver, xsize, c_mode, error)

global property;

%setting the DSVERIFIER_HOME
dsv_setup();

%translate to ANSI-C file
dsv_parser(system,'cl', error);

%verifying using DSVerifier command-line
property = 'QUANTIZATION_ERROR_CLOSED_LOOP';
command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc ' --solver ' solver ' --connection-mode ' c_mode];
dsv_verification(command_line);

%report the verification
output = dsv_report('output.out');
disp(output);

end

