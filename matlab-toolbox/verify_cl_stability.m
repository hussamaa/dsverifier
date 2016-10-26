function verify_cl_stability(system, bmc, realization, solver, xsize, c_mode)

global property;

%setting the DSVERIFIER_HOME
dsv_setup();

%translate to ANSI-C file
dsv_parser(system,'cl',0);

%verifying using DSVerifier command-line
property = 'STABILITY_CLOSED_LOOP';
command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc ' --solver ' solver ' --connection-mode ' c_mode];
dsv_verification(command_line,'cl');

%report the verification
output = dsv_report('output.out','cl');
disp(output);

end

