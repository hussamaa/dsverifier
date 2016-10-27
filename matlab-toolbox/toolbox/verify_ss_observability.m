function verify_ss_observability(system, bmc, realization, xsize)

global property;
%setting the DSVERIFIER_HOME
dsv_setup();
%translate to ANSI-C file
dsv_parser(system,'ss',0);
%verifying using DSVerifier command-line
property = 'OBSERVABILITY';
command_line = [' --property ' property ' --realization ' realization ' --x-size ' num2str(xsize) ' --bmc ' bmc];
dsv_verification(command_line,'ss');
%report the verification
output = dsv_report('output.out','ss');
disp(output);

end

