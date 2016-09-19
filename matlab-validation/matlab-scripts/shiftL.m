function [z_out] = shiftL(zIn,z, nZ)
%
% [z_out] = shiftL(zIn,z, nZ)
% 
% Function developed to support the realizations (DFI,DFII and TDFII)
% The main objective of this function is flip the vector in the right-left
% direction and including a value in the end of vector in each interaction of the realization.
%
% Lennon Chaves
% September 18, 2016
% Manaus

for i=1:(nZ-1)
    z(i) = z(i+1);
end

z(nZ) = zIn;
z_out = z;
end
