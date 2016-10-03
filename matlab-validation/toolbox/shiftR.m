function [z_out] = shiftR(zIn, z, nZ)
%
% [z_out] = shiftR(zIn,z, nZ)
% 
% Function developed to support the realizations (DFI,DFII and TDFII)
% The main objective of this function is flip the vector in the left-right
% direction and including a value in the beginning of vector in each interaction of the realization.
%
% Lennon Chaves
% September 18, 2016
% Manaus

for i=nZ:-1:2
    z(i) = z(i-1);
end

z(1) = zIn;

z_out = z;

end
