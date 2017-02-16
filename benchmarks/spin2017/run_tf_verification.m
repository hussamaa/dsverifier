disp('Verifying Transfer-Function Stability')
%Verify Stability
for i=1:length(controller_daes)
    message = ['DAES: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyStability(controller_daes(i).system, controller_daes(i).int_bits, controller_daes(i).frac_bits, controller_daes(i).rangeMax, controller_daes(i).rangeMin, controller_daes(i).realization, 'CBMC', '', '', '', '', 600)
end

for i=1:length(controller_vant)
    message = ['VANT: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyStability(controller_vant(i).system, controller_vant(i).int_bits, controller_vant(i).frac_bits, controller_vant(i).rangeMax, controller_vant(i).rangeMin, controller_vant(i).realization, 'CBMC', '', '', '', '', 600)
end

disp('Verifying Transfer-Function Minimum Phase')
%Verify Minimum-Phase

for i=1:length(controller_daes)
    message = ['DAES: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyMinimumPhase(controller_daes(i).system, controller_daes(i).int_bits, controller_daes(i).frac_bits, controller_daes(i).rangeMax, controller_daes(i).rangeMin, controller_daes(i).realization, 'CBMC', '', '', '', '', 600)
end

for i=1:length(controller_vant)
    message = ['VANT: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyMinimumPhase(controller_vant(i).system, controller_vant(i).int_bits, controller_vant(i).frac_bits, controller_vant(i).rangeMax, controller_vant(i).rangeMin, controller_vant(i).realization, 'CBMC', '', '', '', '', 600)
end

disp('Verifying Transfer-Function Overflow')
%Verify Overflow

for i=1:length(controller_daes)
    message = ['DAES: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyOverflow(controller_daes(i).system, controller_daes(i).int_bits, controller_daes(i).frac_bits, controller_daes(i).rangeMax, controller_daes(i).rangeMin, controller_daes(i).realization, 10, 'CBMC', '', '', '', '', 600)
end

for i=1:length(controller_vant)
    message = ['VANT: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyOverflow(controller_vant(i).system, controller_vant(i).int_bits, controller_vant(i).frac_bits, controller_vant(i).rangeMax, controller_vant(i).rangeMin, controller_vant(i).realization, 10, 'CBMC', '', '', '', '', 600)
end

disp('Verifying Transfer-Function Limit Cycle')
%Verify Limit-Cycle

for i=1:length(controller_daes)
    message = ['DAES: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyLimitCycle(controller_daes(i).system, controller_daes(i).int_bits, controller_daes(i).frac_bits, controller_daes(i).rangeMax, controller_daes(i).rangeMin, controller_daes(i).realization, 10, 'CBMC', '', '', '', '', 600)
end

for i=1:length(controller_vant)
    message = ['VANT: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyLimitCycle(controller_vant(i).system, controller_vant(i).int_bits, controller_vant(i).frac_bits, controller_vant(i).rangeMax, controller_vant(i).rangeMin, controller_vant(i).realization, 10, 'CBMC', '', '', '', '', 600)
end

disp('Verifying Transfer-Function Quantization Error')
%Verify Quantization Error

for i=1:length(controller_daes)
    message = ['DAES: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyError(controller_daes(i).system, controller_daes(i).int_bits, controller_daes(i).frac_bits, controller_daes(i).rangeMax, controller_daes(i).rangeMin, controller_daes(i).realization, 10, 0.18, 'CBMC', '', '', '', '', 600)
end

for i=1:length(controller_vant)
    message = ['VANT: Verifying Digital System ' num2str(i)];
    disp(message)
    verifyError(controller_vant(i).system, controller_vant(i).int_bits, controller_vant(i).frac_bits, controller_vant(i).rangeMax, controller_vant(i).rangeMin, controller_vant(i).realization, 10, 018, 'CBMC', '', '', '', '', 600)
end
disp('End of Verification of Transfer-Function')