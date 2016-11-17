function check_exhaustively_limit_cycle(system, y0 ,f)

numerator = cell2mat(system.Numerator);
denominator = cell2mat(system.Denominator);

numeratorfwl=(2^(-1*f))*floor(numerator*(2^f));
denominatorfwl=(2^(-1*f))*floor(denominator*(2^f));

polesfwl = roots(denominatorfwl);
delta_error = 0.18;

I = 1;
l = length(polesfwl);

product = 1;
for i=1:l
product = product*1/(1-polesfwl(i)-delta_error);
end

M = abs(I*product);

Tmax = (2*round(M)+1)^l;
count = 1;
output = 'unstable filter';
newstates = 1;

while(count <= Tmax)
    
    yn = dlsim(numeratorfwl, denominatorfwl, y0);
    y0 = yn;
    
    %verificando se yn pertence a U
    flag1 = 1;
    for i=1:length(yn)
          if ~(abs(yn(i)) <= M)
              flag1 = 0;
              newstates = newstates + 1;
              break;
          end
    end
    %verificando se yn for diferente de 0
    flag2 = 1;
    if (flag1 == 1)
        for i=1:length(yn)
            if (yn(i) == 0)
             flag2 = 0;
             newstates = newstates + 1;
             break;
            end
        end
    end
    %verificando se atingiu o numero maximo de recursões
    if (flag2 == 1)
       if (count == Tmax)
         output = 'unstable filter';
       end
    end
             
    if (flag1 == 1) && (count < Tmax)
        output = 'stable filter';
        break
    end
    
    count = count + 1;    
end


disp(output);

end