%% Script to verify and compare the results between MATLAB and DSVerifier

% Open the file with validation of counterexamples by MATLAB
fileID = fopen('../outputs/dsv_matlab_filter_outputs.txt','r');

formatSpec = '%f %f %f %f %f %f %f %f %f %f';

% Matrix of Counteexamples validation by MATLAB
DSV_MATLAB = textscan(fileID,formatSpec);

fclose(fileID);

% Open the file with validation of counterexamples by MATLAB
fileID = fopen('../outputs/dsv_counterexamples_outputs.txt','r');

% Matrix of Counteexamples validation by MATLAB
DSV_COUNTEREXAMPLES = textscan(fileID,formatSpec);

fclose(fileID);

for i=1:n
    count = 0;
    for j=1:size_out
        
        vec_matlab = DSV_MATLAB{1,j};
        vec_counter = DSV_COUNTEREXAMPLES{1,j};
        item_matlab = vec_matlab(i);
        item_counter = vec_counter(i);
        
        if item_matlab == item_counter
            count = j;
        end
        
    end
    
    if count == size_out
        feedback = ['echo ' 'Teste-' num2str(i) 'Status: Successful'];
    else
        feedback = ['echo ' 'Teste-' num2str(i) ' Status: Failed'];
    end
    system(feedback);
end