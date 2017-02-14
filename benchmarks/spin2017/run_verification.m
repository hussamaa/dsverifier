close all
clear all
clc

%Running Verification for Transfer-Function:

disp('Running TF Stability');
run_verification_tf_stability

disp('Running TF Minimum Phase');
run_verification_tf_minimum_phase

disp('Running TF Overflow');
run_verification_tf_overflow

disp('Running TF Limit Cycle');
run_verification_tf_limit_cycle

disp('Running TF Quantization Error');
run_verification_tf_error

%Running Verification for State-Space:

disp('Running SS Stability');
run_verification_ss_stability

disp('Running SS Observability');
run_verification_ss_observability

disp('Running SS Controllability');
run_verification_ss_controllability

disp('Running SS Quantization Error');
run_verification_ss_quantization_error
