with Ada.Text_IO;       use Ada.Text_IO;
with Ada.Float_Text_IO; use Ada.Float_Text_IO;
with Vecteurs_Creux;    use Vecteurs_Creux;

-- Exemple d'utilisation des vecteurs creux.
procedure Exemple_Vecteurs_Creux is

	V,V2 : T_Vecteur_Creux;

	Epsilon: constant Float := 1.0e-5;
begin
	Put_Line ("Début du scénario");
    Initialiser(V);


    Put ("Itératif : ");
    Put(Composante_Iteratif(V,2));
    new_line;

    Put ("Récursif : ");
    Put(Composante_Recursif(V,2));
    new_line;



    Initialiser(V2);

    Put("V=V2 : ");
    New_Line;
    Put ("Itératif : ");
    --Put(Sont_Egaux_Iteratif(V, V2));
    New_Line;
    --Put ("Récursif : ");
    --Put(Sont_Egaux_Récursirf(V, V2));
    New_Line;


    Detruire(V);
    Detruire(V2);
	Put_Line ("Fin du scénario");
end Exemple_Vecteurs_Creux;
