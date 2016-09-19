%
%% Script developed to simulate automatically all counterexamples 
%% by realization form (DFI, DFII and TDFII)

fileOutputID = fopen('../outputs/dsv_matlab_model_outputs.txt','w');
for i=1:n
    realization_form = realization(i:i);

    initial0=initial_states.a(i:i);
    initial1=initial_states.b(i:i);
    initial2=initial_states.c(i:i);
    
    sml_initial_states = [initial0 initial1 initial2];
    sml_input_const = inputs_consts(i:i);
    sml_prec_int = prec_bit(i:i);
    sml_prec_frac = prec_frac(i:i);
    sml_a0 = a0(i:i);
    sml_a1 = a1(i:i);
    sml_a2 = a2(i:i);
    sml_b0 = b0(i:i);
    sml_b1 = b1(i:i);
    sml_b2 = b2(i:i);

    if strcmp(realization_form,'DFI')
        model = '../model-simulink/direct_form_I';
        sim(model);
        output = output_DFI.signals.values';
    elseif strcmp(realization_form,'DFII')
        model = '../model-simulink/direct_form_II';
        sim(model);
        output =  output_DFII.signals.values';
    elseif strcmp(realization_form,'TDFII')
        model = '../model-simulink/transposed_direct_form_II';
        sim(model);
        output =  output_TDFII.signals.values';
    end
    
    fprintf(fileOutputID,'%f %f %f %f %f %f %f %f %f %f\n',output);
end
fclose(fileOutputID);
