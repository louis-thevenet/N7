/* Problème du voyageur de Commerce */


###############################  Model ###############################


###############################  Sets  ###############################

set CLIENTS;

################### Variables ###################

var M{i in CLIENTS, j in CLIENTS}, binary; # 1 si on va du client i au client j, 0 sinon
var u{i in CLIENTS}, integer; # ordre de livraison


###################  Constants: Data to load   #########################

param distances{i in CLIENTS, j in CLIENTS};
param n,integer;
################### Constraints ###################

s.t. TousClientsServisUneFois{i in CLIENTS}:
	sum{j in CLIENTS} M[i,j] = 1;

s.t. TousClientsQuittesUneFois{j in CLIENTS}:
    sum{i in CLIENTS} M[i,j] = 1;

    s.t. UneFoisParClient{j in CLIENTS}:
    M[j,j] = 0;

s.t. ordrePositif{i in CLIENTS}:
    u[i] >= 0;

s.t. PasDeDetour{i in CLIENTS, j in CLIENTS}:
    u[i] + 1 <= (1-M[i,j])*100000 + u[j];


###### Objective ######
minimize DistanceTotale:
	sum{i in CLIENTS, j in CLIENTS} M[i,j]*distances[i,j];

#default data

data;
param n := 6;

set CLIENTS :=
Alpha
C1
C2
C3
C4
C5;


param distances: Alpha C1 C2 C3 C4 C5 :=
                 Alpha  0  1  1 10 12 12
                 C1  1  0  1  8 10 11
                 C2  1  1  0  8 11 10
                 C3 10  8  8  0  1  1
                 C4 12 10 11  1  0  1
                 C5 12 11 10  1  1  0;

end;

