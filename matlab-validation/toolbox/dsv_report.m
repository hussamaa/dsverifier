function dsv_report(digital_system)
%
% Script to generate a report about automatic validation
%
% Function: dsv_report(digital_system) 
%
% where digital_system is a .MAT File generated
% by automatic validation of counterexamples.
%
% the digital_system could be a vector with a lot of counterexamples and composed by a lot of 'systems'.
%
% The struct 'digital_system' should have the following features:
% system.sys.a = denominator;
% system.sys.b = numerator;
% system.sys.tf = transfer function system representation
% system.impl.frac_bits = fractionary bits
% system.impl.int_bits = integer bits
% system.impl.realization_form = realization, and it should be DFI, DFII, TDFII, DDFI, DDFII or TDDFII
% system.inputs.const_inputs = the inputs from counterexample
% system.inputs.initial_states = the initial states from counterexample
% system.outputs.output_verification = the output extracted from counterexample
% system.impl.delta = in delta form realizations, the delta operator should be informed
% system.impl.sample_time = sample time of realization
% system.impl.x_size = the bound size
%
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

total_successful = 0;
total_failed = 0;
total_time_execution = 0;

disp(' ')
disp('Counterexamples Validation Report...');
disp(' ')
for i=1:length(digital_system)
    time_execution = digital_system(i).output.time_execution;
    status = lower(strtrim(digital_system(i).status));
 
    total_time_execution = total_time_execution + time_execution;
    
    if (strcmp(status, 'successful'))
        total_successful = total_successful + 1;
    elseif (strcmp(status, 'failed'))
        total_failed = total_failed + 1;
    end
    message = ['Test case ' num2str(i) ' time: ' num2str(time_execution) ' status: ' status];
    disp(message);
end
disp(' ')
disp('General Report:');
disp(' ')
total_tests = total_failed + total_successful;
show_total_success = ['Total Successull: ' num2str(total_successful)];
show_total_failed = ['Total Failed: ' num2str(total_failed)];
show_total_test = ['Total Tests: ' num2str(total_tests)];
show_total_execution = ['Total Time Execution: ' num2str(total_time_execution)];

disp(show_total_success);
disp(show_total_failed);
disp(show_total_test);
disp(show_total_execution);

if total_successful > total_failed
    max_disp = total_successful + 2;
else
    max_disp = total_failed + 2;
end 
%% Generate Graphics
%Successful vs Failed
p1X = [1 2]; p1Y = [total_successful 0];
p2X = [3 4]; p2Y = [0 total_failed];
p1 = bar(p1X,p1Y);
text(1,total_successful+0.5,num2str(total_successful))
hold on;
p2 = bar(p2X,p2Y);
text(4,total_failed+0.5,num2str(total_failed))
set(p1,'FaceColor','green');
set(p2,'FaceColor','red');
ylabel('Test Cases');
axis([0 5 1 max_disp])
legend('Sucessfull Tests','Failed Tests');
title('Graphic about Successful and Failed Tests');
grid on;
set(gca,'xticklabel',{[]}) 

end
