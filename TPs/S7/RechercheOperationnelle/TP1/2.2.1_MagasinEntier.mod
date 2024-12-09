
###############################  Model ###############################


###############################  Sets  ###############################

set FLUIDES;
set MAGASINS;
set DEMANDES;

################### Variables ###################

var D{i in FLUIDES, j in MAGASINS, k in DEMANDES}, integer >=0; 

###################  Constants: Data to load   #########################

param fluides_par_demandes{i in DEMANDES, j in FLUIDES};
param stock_par_magasin{i in MAGASINS, j in FLUIDES};
param cout_par_magasin{i in MAGASINS, j in FLUIDES};

################### Constraints ###################

s.t. RespectStock{i in FLUIDES, j in MAGASINS}:
	sum{k in DEMANDES} D[i,j,k] <= stock_par_magasin[j,i];


s.t. RespectDemande{i in FLUIDES, k in DEMANDES}:
sum{j in MAGASINS} D[i,j,k]= fluides_par_demandes[k, i];

###### Objective ######
minimize CoutTotal:
	sum{i in FLUIDES, j in MAGASINS,  k in DEMANDES} cout_par_magasin[j,i] * D[i,j,k];

#default data

data;

set FLUIDES:= 
F1
F2;

set MAGASINS :=
M1
M2
M3;

set DEMANDES :=
D1
D2;

param fluides_par_demandes: F1 F2 :=
D1 2 0
D2 1 3;

param stock_par_magasin: F1 F2 :=
M1 2.5 1
M2 1 2
M3 2 1;

param cout_par_magasin: F1 F2 :=
M1 1 1
M2 2 3
M3 3 2;

end;

