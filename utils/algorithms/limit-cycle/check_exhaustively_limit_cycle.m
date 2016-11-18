function check_exhaustively_limit_cycle(num,den, y0 ,f , I, id)

numerator = num;
denominator = den;

numeratorfwl=(2^(-1*f))*round(numerator*(2^f));
denominatorfwl=(2^(-1*f))*round(denominator*(2^f));

polesfwl = roots(denominatorfwl);
delta_error = 0.018;

l = length(polesfwl);

product = 1;
for i=1:l
product = product*(1/(1-polesfwl(i)-delta_error));
end

M = abs(I*product);

Tmax = 2^(l-1)*(ceil(M)+1)^l;

Tmax = Tmax^2;

count = 1;
output = 'unstable filter';
current_state = 1;

yn = filter(numeratorfwl, denominatorfwl, y0);

%check BIBO in output
isbibo = 1;

for i=1:length(yn)
   if (abs(yn) > M)
       isbibo = 0;
       break;
    end
end

max_states = length(y0);
unstable = 0;

while(count <= Tmax)
    
    yn_1 = yn(current_state);
    %verificando se yn pertence a U
    flag1 = 1;
    if ~(abs(yn_1) < M)
       flag1 = 0;
       current_state = current_state + 1;
    end
    %verificando se yn for diferente de 0
    flag2 = 1;
    if (flag1 == 1)
        if (yn_1 == 0)
           flag2 = 0;
           current_state = current_state + 1;
        end
    end
    
    if (current_state >= max_states )
        output = 'Absence of Limit Cycle';
        break
    end
    
    %verificando se atingiu o numero maximo de recursões
    if (flag2 == 1 && flag1 == 1)
       if (count == Tmax)
         unstable = 1;
         break
       end
    end
    
    count = count + 1;    
end

   if ~(isbibo) || unstable
       output =  'unstable filter';
   end
   
   response = ['Test Case ' num2str(id) ' - ' output];
   disp(response);

end