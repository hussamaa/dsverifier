function [system] = dsv_parser()
%
% Script to keep counterexamples parameters in variables on workspace
% [system] = dsv_parser()
% The output of this function is the counterexamples extracted in variables
% on MATLAB workspace.
%
% Lennon Chaves
% September 20, 2016
% Manaus


fileID = fopen('outputs/dsv_counterexample_parameters.txt','r');
fileIDS = fopen('outputs/dsv_n_size.txt','r');

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
n_size = textscan(fileIDS,'%d');
n = n_size{1};
fclose(fileIDS);
delete 'outputs/dsv_n_size.txt','r';
% Number of outputs/inputs used in Limit Cycle.
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

% Open the file with validation of counterexamples by MATLAB
fileID = fopen('outputs/dsv_counterexamples_outputs.txt','r');

% Matrix of Counteexamples validation by MATLAB
output_counterexamples = textscan(fileID,'%f %f %f %f %f %f %f %f %f %f');
fclose(fileID);

out1 = output_counterexamples{1,1};
out2 = output_counterexamples{1,2};
out3 = output_counterexamples{1,3};
out4 = output_counterexamples{1,4};
out5 = output_counterexamples{1,5};
out6 = output_counterexamples{1,6};
out7 = output_counterexamples{1,7};
out8 = output_counterexamples{1,8};
out9 = output_counterexamples{1,9};
out10 = output_counterexamples{1,10};


%% Organizing variables as system struct

for i=1:n
    system(i).test_case = name(i);
    denominator = [a0(i) a1(i) a2(i)];
    system(i).sys.a = denominator;
    numerator = [b0(i) b1(i) b1(i)];
    system(i).sys.b = numerator;
    system(i).sys.tf = tf(numerator,denominator,1);
    system(i).inputs.initial_states = [initial_states.a(i) initial_states.b(i) initial_states.c(i)];
    system(i).inputs.const_inputs = repmat(inputs_consts(i),1,input_times(i));
    system(i).impl.int_bits = prec_bit(i);
    system(i).impl.frac_bits = prec_frac(i);
    system(i).impl.x_size = input_times(i);
    system(i).impl.realization_form = realization(i);
    system(i).output.output_verification = [out1(i) out2(i) out3(i) out4(i) out5(i) out6(i) out7(i) out8(i) out9(i) out10(i)];
end

end
