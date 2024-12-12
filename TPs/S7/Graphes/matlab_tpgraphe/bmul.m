%boolean matrix multuplication
function C=bmul(A,B)
C=double(A>0)*double(B>0);
C=double(C>0);