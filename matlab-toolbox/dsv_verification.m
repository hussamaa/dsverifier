function dsv_verification(command, representation)

if strcmp(representation,'ss')
s1 = './dsverifier file.ss';
else
s1 = './dsverifier input.c';
end

s3 = ' --show-ce-data > output.out';
command_line = [s1 command s3];
system(command_line);

end

