%Verify Stability
disp('Verifying Transfer-Function Stability')
for i=1:10
    message = ['DAES: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyStability(controller_daes(i).system, controller_daes(i).int_bits, controller_daes(i).frac_bits, controller_daes(i).rangeMax, controller_daes(i).rangeMin, controller_daes(i).realization, 'ESBMC', '', '', '', '', 600)
end

for i=1:length(controller_UAV)
    message = ['UAV: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyStability(controller_UAV(i).system, controller_UAV(i).int_bits, controller_UAV(i).frac_bits, controller_UAV(i).rangeMax, controller_UAV(i).rangeMin, controller_UAV(i).realization, 'ESBMC', '', '', '', '', 600)
end

disp('Verifying Transfer-Function Minimum Phase')
%Verify Minimum-Phase

for i=1:10
    message = ['DAES: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyMinimumPhase(controller_daes(i).system, controller_daes(i).int_bits, controller_daes(i).frac_bits, controller_daes(i).rangeMax, controller_daes(i).rangeMin, controller_daes(i).realization, 'ESBMC', '', '', '', '', 600)
end

for i=1:length(controller_UAV)
    message = ['UAV: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyMinimumPhase(controller_UAV(i).system, controller_UAV(i).int_bits, controller_UAV(i).frac_bits, controller_UAV(i).rangeMax, controller_UAV(i).rangeMin, controller_UAV(i).realization, 'ESBMC', '', '', '', '', 600)
end

disp('Verifying Transfer-Function Overflow')
%Verify Overflow

for i=1:10
    message = ['DAES: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyOverflow(controller_daes(i).system, controller_daes(i).int_bits, controller_daes(i).frac_bits, controller_daes(i).rangeMax, controller_daes(i).rangeMin, controller_daes(i).realization, 10, 'ESBMC', '', '', '', '', 600)
end

for i=1:length(controller_UAV)
    message = ['UAV: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyOverflow(controller_UAV(i).system, controller_UAV(i).int_bits, controller_UAV(i).frac_bits, controller_UAV(i).rangeMax, controller_UAV(i).rangeMin, controller_UAV(i).realization, 10, 'ESBMC', '', '', '', '', 600)
end

disp('Verifying Transfer-Function Limit Cycle')
%Verify Limit-Cycle

for i=1:10
    message = ['DAES: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyLimitCycle(controller_daes(i).system, controller_daes(i).int_bits, controller_daes(i).frac_bits, controller_daes(i).rangeMax, controller_daes(i).rangeMin, controller_daes(i).realization, 10, 'ESBMC', '', '', '', '', 600)
end

for i=1:length(controller_UAV)
    message = ['UAV: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyLimitCycle(controller_UAV(i).system, controller_UAV(i).int_bits, controller_UAV(i).frac_bits, controller_UAV(i).rangeMax, controller_UAV(i).rangeMin, controller_UAV(i).realization, 10, 'ESBMC', '', '', '', '', 600)
end

disp('Verifying Transfer-Function Quantization Error')
%Verify Quantization Error

for i=1:10
    message = ['DAES: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyError(controller_daes(i).system, controller_daes(i).int_bits, controller_daes(i).frac_bits, controller_daes(i).rangeMax, controller_daes(i).rangeMin, controller_daes(i).realization, 10, 0.18, 'ESBMC', '', '', '', '', 600)
end

for i=1:length(controller_UAV)
    message = ['UAV: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyError(controller_UAV(i).system, controller_UAV(i).int_bits, controller_UAV(i).frac_bits, controller_UAV(i).rangeMax, controller_UAV(i).rangeMin, controller_UAV(i).realization, 10, 0.18, 'ESBMC', '', '', '', '', 600)
end
disp('End of Verification of Transfer-Function')