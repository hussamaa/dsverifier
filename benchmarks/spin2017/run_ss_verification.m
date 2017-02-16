disp('Verifying State-Space Stability')
%Verify Stability
for i=1:length(controller_ss)
    message = ['Verifying Digital System ' num2str(i)];
    disp(message)
    verifyStateSpaceStability(controller_ss(i).system, 1.0, 8, 7, 1, -1, '');
end
disp('Verifying State-Space Controllability')
%Verify Controllability
for i=1:length(controller_ss)
    message = ['Verifying Digital System ' num2str(i)];
    disp(message)
    verifyStateSpaceControllability(controller_ss(i).system, 1.0, 8, 7, 1, -1,'');
end
disp('Verifying State-Space Observability')
%Verify Observability
for i=1:length(controller_ss)
    message = ['Verifying Digital System ' num2str(i)];
    disp(message)
    verifyStateSpaceObservability(controller_ss(i).system, 1.0, 8, 7, 1, -1,'');
end
disp('Verifying State-Space Quantization Error')
%Verify Quantization Error
for i=1:length(controller_ss)
    message = ['Verifying Digital System ' num2str(i)];
    disp(message)
    verifyStateSpaceQuantizationError(controller_ss(i).system, 1.0, 8, 7, 1, -1, 0.18, 10,'');
end
disp('End of Verification of State-Space')