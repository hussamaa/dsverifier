% TOOLBOX
%
% Files
%   dsv_parser                   - Reads the system in struct form and translate to a ANSI-C file
%   dsv_report                   - Shows the report about the verification: successful or failed
%   dsv_setup                    - Setup the DSVERIFIER_HOME and model checkers visibility in a variable environment
%   dsv_verification             - Function to get the parameters, system and implementatio to start the verification
%   gen_counterexample           - Translate .out file generated after verification to a .MAT file with
%   get_macro_params             - Support function to get the extra params in order to add in command line
%   matrix2string                - Translate a matrix representation to a string representation
%   poly2strc                    - Translate a polynomial representation to a string representation
%   verify_cl_limit_cycle        - Checks limit cycle property violation for closed-loop digital systems using a bounded model checking tool.
%   verify_cl_quantization_error - Checks quantization error property violation for closed-loop digital systems using a bounded model checking tool.
%   verify_cl_stability          - Checks robust stability property violation for closed-loop digital systems using a bounded model checking tool.
%   verify_error                 - Checks error property violation for digital systems using a bounded model checking tool.
%   verify_limit_cycle           - Checks limit cycle property violation for digital systems using a bounded model checking tool.
%   verify_minimum_phase         - Checks minimum phase property violation for digital systems using a bounded model checking tool.
%   verify_overflow              - Checks overflow property violation for digital systems using a bounded model checking tool.
%   verify_ss_controllability    - Checks controllability property violation for digital systems (state-space representation) using a bounded model checking tool.
%   verify_ss_limit_cycle        - Checks limit cycle property violation for digital systems (state-space representation) using a bounded model checking tool.
%   verify_ss_observability      - Checks observability property violation for digital systems (state-space representation) using a bounded model checking tool.
%   verify_ss_quantization_error - Checks quantization error property violation for digital systems (state-space representation) using a bounded model checking tool.
%   verify_ss_stability          - Checks stability property violation for digital systems (state-space representation) using a bounded model checking tool.
%   verify_stability             - Checks stability property violation for digital systems using a bounded model checking tool.
%   verify_timing                - Checks timing property violation for digital systems using a bounded model checking tool.
