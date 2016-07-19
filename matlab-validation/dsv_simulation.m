%% Script developed to simulate automatically all counterexamples by realization
for i=1:n
    realization_form = realization(i:i);
    
    initial0=initial_states.a(i:i);
    initial1=initial_states.b(i:i);
    initial2=initial_states.c(i:i);
    
    sml_initial_states = [initial0 initial1 initial2];
    sml_input_const = inputs_consts(i:i);
    sml_prec_int = prec_bit(i:i);
    sml_prec_frac = prec_frac(i:i);
    
    if strcmp(realization_form,'DFI')
        sim('model-simulink/direct_form_I');
    elseif strcmp(realization_form,'DFII')
        sim('model-simulink/direct_form_II');
    elseif strcmp(realization_form,'TDFII')
        sim('model-simulink/transposed_direct_form_II');
    end
    
end