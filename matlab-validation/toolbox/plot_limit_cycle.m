function signal = plot_limit_cycle(system)


y = system.output.output_verification;
stairs(y);
title('Graphic Generated for Limit Cycle Output');
ylabel ('Outputs (y)');
xlabel ('Time (x size)');

signal = y;

end
