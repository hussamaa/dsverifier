function output = matrix2string( matrix )

[r,c]= size(matrix);
linha = '[';
for i=1:r
    for j=1:c
        element = matrix(i,j);
        linha = strcat(linha,num2str(element));
        if(j ~= c)
         linha = strcat(linha,',');
        end
    end
       if(i ~= r)
         linha = strcat(linha,';');
       end
end
linha = strcat(linha,']');
output = linha;
end

