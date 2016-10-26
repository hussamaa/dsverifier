function dsv_parser(ds, type)
%read system struct and translate to a ANSI-C file

if strcmp(type, 'tf')
a = cell2mat(ds.system.Denominator);
nA = length(a);
b = cell2mat(ds.system.Numerator);
nB = length(b);
sample_time = ds.system.Ts;
frac_bits = ds.impl.frac_bits;
int_bits = ds.impl.int_bits;
max_range = ds.range.max;
min_range = ds.range.min;
delta = ds.delta;

fid = fopen('input.c', 'wt' );
fprintf(fid,'%s\n\n', '#include <dsverifier.h>');
fprintf(fid,'%s\n\t', 'digital_system ds = { ');
fprintf(fid,'%s %s },\n\t','.b = { ', replace(num2str(b),'  ', ', '));
fprintf(fid,'%s %d,\n\t','.b_size = ', nB);
fprintf(fid,'%s %s },\n\t','.a = { ', replace(num2str(a),'  ', ', '));
fprintf(fid,'%s %d,\n\t','.a_size = ', nA);
fprintf(fid,'%s %d\n','.sample_time =', sample_time);
fprintf(fid,'%s\n\n','};');
fprintf(fid,'%s\n\t','implementation impl = { ');
fprintf(fid,'%s %d,\n\t','.int_bits = ', int_bits);
fprintf(fid,'%s %d,\n\t','.frac_bits =  ', frac_bits);
fprintf(fid,'%s %d,\n\t','.max = ', max_range);
fprintf(fid,'%s %d,\n\t','.min = ', min_range);
fprintf(fid,'%s %d\n','.delta =', delta);
fprintf(fid,'%s\n\n','};');
fclose(fid);
elseif strcmp(type, 'cl')
    
elseif strcmp(type, 'ss')
    
end

end

