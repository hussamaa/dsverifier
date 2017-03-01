disp('Verifying Closed-Loop Stability')
%Verify Stability
for i=1:length(digital_system)
    message = ['Verifying Digital System ' num2str(i)];
    disp(message)
    verifyClosedLoopStability(digital_system(i).controller, digital_system(i).plant, digital_system(i).int_bits, digital_system(i).frac_bits, digital_system(i).rangeMax, digital_system(i).rangeMin, digital_system(i).realization, 'SERIES', 'ESBMC','','','','',3600);
end

disp('Verifying Closed-Loop Limit-Cycle')
%Verify Limit-Cycle
for i=1:length(digital_system)
    message = ['Verifying Digital System ' num2str(i)];
    disp(message)
    verifyClosedLoopLimitCycle(digital_system(i).controller, digital_system(i).plant, digital_system(i).int_bits, digital_system(i).frac_bits, digital_system(i).rangeMax, digital_system(i).rangeMin, digital_system(i).realization, 10, 'SERIES', 'ESBMC','','','','',3600);
end

disp('Verifying Closed-Loop Quantization Error')
%Verify Quantization Error
for i=1:length(digital_system)
    message = ['Verifying Digital System ' num2str(i)];
    disp(message)
    verifyClosedLoopQuantizationError(digital_system(i).controller, digital_system(i).plant, digital_system(i).int_bits, digital_system(i).frac_bits, digital_system(i).rangeMax, digital_system(i).rangeMin, digital_system(i).realization, 10, 0.18, 'SERIES','','','','',3600);
end

disp('End of Verification of Closed-Loop')
