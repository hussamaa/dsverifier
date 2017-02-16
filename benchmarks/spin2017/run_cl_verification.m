disp('Verifying Closed-Loop Stability')
%Verify Stability
for i=1:length(digital_system)
    message = ['Verifying Digital System ' num2str(i)];
    disp(message)
    verifyClosedLoopStability(digital_system(i).controller, digital_system(i).plant, digital_system(i).int_bits, digital_system(i).frac_bits, digital_system(i).rangeMax, digital_system(i).rangeMin, digital_system(i).realization, 'SERIES');
end

disp('End of Verification of Closed-Loop')
