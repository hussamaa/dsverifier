function dsv_verification(s2)

s1 = 'dsverifier input.c';
s3 = ' > output.out';
command_line = [s1 s2 s3];
system(command_line);

end

