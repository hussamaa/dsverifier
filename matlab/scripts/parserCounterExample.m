%% Script developed to extract counter examples and put the values on workspace
% Open the file with counter examples
fileID = fopen('counter_examples.txt','r');
%% Format Specification: 
% b0 b1 b2 a0 a1 a2 initial_states inputs integer_bits fraction_bits
% input_times signal_times
formatSpec = '%f %f %f %f %f %f %f %f %d %d %f %d';
% Size of Counter Example: depends the number of parameters to be parsed
sizeCE = [12 Inf];
% Matrix of Counter Examples extracted
CE = fscanf(fileID,formatSpec, sizeCE);
fclose(fileID);
% Number of counter examples. It must be changed because depends the number
% of counter examples.
n = 8;
% Matrix transposed of counter examples
CE = CE';
% Extract values from Matrix of Counter Examples to vectorizing the
% parameters to be used on Simulink
b0 = CE(1:n,1)';
b1 = CE(1:n,2)';
b2 = CE(1:n,3)';
a0 = CE(1:n,4)';
a1 = CE(1:n,5)';
a2 = CE(1:n,6)';
% Vectors about initial states and constant inputs (to be used on delays)
initial_states = CE(1:n,7)';
const_inputs = CE(1:n,8)';

% Parameters about integer and fraction bits
prec_bit = CE(1:n,9)';
prec_frac = CE(1:n,10)';

% Parameters about Inputs. It have to be used with repmat function,
% according to the number of repetions about inputs.
input_times = CE(1:n,12)';
input_signal = CE(1:n,11)';