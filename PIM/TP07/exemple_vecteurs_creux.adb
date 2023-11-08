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


    New_Line;
    Put("On modifie V(5)");
    New_Line;
    Modifier(V, 5, 2.0);
    New_Line;
    Afficher(V);
    New_Line;

    Afficher(V);

    New_Line;



    Initialiser(V2);
    Modifier(V2, 5, 2.0);


    pragma Assert (Sont_Egaux_Recursif(V, V2));
    pragma Assert (Sont_Egaux_Iteratif(V, V2));

    Modifier(V, 2, 2.0);
    Modifier(V2, 8, 2.0);
    Modifier(V, 8, 2.0);


    Put(Produit_Scalaire(V, V2));
    New_Line;

    Afficher(V);
    new_line;
    Afficher(V2);
New_Line;
    Additionner(V, V2);
    Afficher(V);
New_Line;
Put(Norme2(V));
    Detruire(V);
    Detruire(V2);
	Put_Line ("Fin du scénario");
end Exemple_Vecteurs_Creux;
