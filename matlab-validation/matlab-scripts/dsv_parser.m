%% Script to put counterexamples parameters in variables on workspace

% Open the file with counter examples
fileID = fopen('../outputs/dsv_counterexample_parameters.txt','r');
%% Format Specification: 
% b0 b1 b2 a0 a1 a2 
% initial_states chama inputs_const integer_bits fraction_bits input_times
% initial_states is generally equals the number of elements of numerator/denominator
formatSpec = '%s %s %d %d %d %d %f %f %f %f %f %f %f %f %f %f';

% Matrix of Counter Examples extracted
CE = textscan(fileID,formatSpec);
fclose(fileID);
% Number of counter examples. It must be changed because depends the number
% of counter examples.
n = 27;
size_out = 10;
% Matrix transposed of counter examples
CE = CE';
% Realization, counterexample file name
realization = CE{1}';
name = CE{2}';
% Parameters about integer and fraction bits
prec_bit = CE{3}';
prec_frac = CE{4}';
% Parameters about Inputs. It have to be used with repmat function,
% according to the number of repetions about inputs.
input_times = CE{5}';
% The systems order
order = CE{6}';
% Extract values from Matrix of Counter Examples to vectorizing the
% parameters to be used on Simulink
b0 = CE{7}';
b1 = CE{8}';
b2 = CE{9}';
a0 = CE{10}';
a1 = CE{11}';
a2 = CE{12}';
% Vectors about initial states and constant inputs (to be used on delays)
initial_states.a = CE{13}';
initial_states.b = CE{14}';
initial_states.c = CE{15}';
% constants inputs
inputs_consts = CE{16}';
%Filter Function
fileOutputID = fopen('../outputs/dsv_matlab_filter_outputs.txt','w');
for i=1:n
    num0=b0(i:i);
    num1=b1(i:i);
    num2=b2(i:i);
    den0=a0(i:i);
    den1=a1(i:i);
    den2=a2(i:i);
    inputs=inputs_consts(i:i);
    initial0=initial_states.a(i:i);
    initial1=initial_states.b(i:i);
    Out = filter([num0 num1 num2],[den0 den1 den2],[inputs inputs inputs inputs inputs inputs inputs inputs inputs inputs],[initial0 initial1]);
    fprintf(fileOutputID,'%f %f %f %f %f %f %f %f %f %f\n',Out);

end 

%printing the outputs in a file
fclose(fileOutputID);