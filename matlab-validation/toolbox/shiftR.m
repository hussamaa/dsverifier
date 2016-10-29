function [z_out] = shiftR(zIn, z, nZ)
%
% Function developed to shift right during the realizations (DFI,DFII and TDFII)
%
% Function: [z_out] = shiftR(zIn,z, nZ)
% 
%
% The main objective of this function is flip the vector in the left-right
% direction and including a value in the beginning of vector in each interaction of the realization.
%
% Lennon Chaves
% October 09, 2016
% Manaus, Brazil

for i=nZ:-1:2
    z(i) = z(i-1);
end

z(1) = zIn;

z_out = z;

end
