
###############################  Model ###############################


###############################  Sets  ###############################

set PERSONNES;
set ACTIVITES;

################### Variables ###################


var M{i in PERSONNES, j in ACTIVITES}, binary; 

###################  Constants: Data to load   #########################

param pref{i in PERSONNES, j in ACTIVITES};

################### Constraints ###################

s.t. RespectDistributionLigne{i in PERSONNES}:
	sum{j in ACTIVITES} M[i,j] = 1;

s.t. RespectDistributionColonne{j in ACTIVITES}:
	sum{i in PERSONNES} M[i,j] = 1;



###### Objective ######

maximize SatisfactionTotale: 
		sum{i in PERSONNES} sum{j in ACTIVITES} (M[i,j] * pref[i,j]);

#default data

data;

set PERSONNES := 
P1
P2
P3;

set ACTIVITES :=
T1
T2
T3;


param pref: T1 T2 T3 :=
P1 9 5 1
P2 2 4 2
P3 9 4 8;


end;
