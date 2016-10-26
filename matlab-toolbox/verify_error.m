function output = verify_error(system, bmc, realization, solver, xsize)

%setting the DSVERIFIER_HOME
dsv_setup();
%translate to ANSI-C file
dsv_parser(system,'tf');
%verifying using DSVerifier command-line
property = 'ERROR';
command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc ' --solver ' solver];
dsv_verification(command_line);
%report the verification
output = dsv_report('output.out');
disp(output);

end

