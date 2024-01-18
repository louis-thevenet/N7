--
--  Les TODO dans le texte vous indique les parties de ce programme à compléter.
--  Les autres parties ne doivent pas être modifiées.
--
with Ada.Text_IO;          use Ada.Text_IO;
with Ada.Integer_Text_IO;  use Ada.Integer_Text_IO;

-- Supprimer certains éléments d'un tableau
procedure Tableau_Supprimer is

    Capacite: constant Integer := 10;   -- Cette taille est arbitraire

    type T_TableauElements is array (1..Capacite) of Integer;

    type T_Tableau is
        record
            Elements: T_TableauElements;
            Taille: Integer;
            -- Invariant: 0 <= Taille and Taille <= Capacite;
        end record;


    -- Objectif : Afficher le tableau.
    --    Les éléments sont affichés entre crochets, séparés par des virgules.
    -- Paramètres :
    --    Tab : le tableau à afficher.
    procedure Ecrire(Tab: in T_Tableau) is
    begin
        Put ('[');
        if Tab.Taille > 0 then
            -- Écrire le premier élément
            Put (Tab.Elements (1), 1);

            -- Écrire les autres éléments précédés d'une virgule
            for I in 2..Tab.Taille loop
                Put (", ");
                Put (Tab.Elements (I), 1);
            end loop;
        else
            null;
        end if;
        Put (']');
    end Ecrire;



    -- TODO : écrire ici le sous-programme demandé



    -- Objectif : Indiquer si deux tableaux son égaux.
    -- Paramètres :
    --     Tab1, Tab2 : les deux tableaux à comparer
    -- Résultat
    --     Vrai si et seulement si Tab1 et Tab2 sont égaux.
    --
    -- Remarque : Ici on redéfinit l'opérateur "=" déjà présent en Ada qui par
    -- défaut compara les tailles et tous les éléments de Elements.
    function "=" (Tab1, Tab2: in T_Tableau) return Boolean is
        Resultat: Boolean;
        Indice: Integer;
    begin
        -- SLICES START DELETE
        return Tab1.Taille = Tab2.Taille
                and then Tab1.Elements (1..Tab1.Taille) = Tab2.Elements (1..Tab1.Taille);
        -- SLICES STOP DELETE
        -- NO_SLICES START DELETE
        if Tab1.Taille /= Tab2.Taille then
            Resultat := False;
        else
            Indice := 1;
            while Indice <= Tab1.Taille
                    and then Tab1.Elements (Indice) = Tab2.Elements (Indice)
            loop
                Indice := Indice + 1;
            end loop;
            Resultat := Indice > Tab1.Taille;
        end if;
        return Resultat;
        -- NO_SLICES STOP DELETE
    end "=";



    -- Programme de test de la procédure Trier.
    procedure Tester_Supprimer is

        procedure Tester(Tab, Attendu: in T_Tableau) is
            Copie: T_Tableau;
        begin
            Copie := Tab;
            -- TODO Appeler le sous-programme qui supprime...
            pragma Assert(Copie = Attendu);
        end Tester;

    begin
        Tester (( (others => 0), 0),
                ( (others => 0), 0));
        Tester (( (1, 20, 0, 19, others => 0), 4),
                ( (1, 20, 0, 19, others => 0), 4));
        Tester (( (1, 20, 0, -1, -2, -3, 19, others => 0), 7),
                ( (1, 20, 0, 19, others => 0), 4));
        Tester (( (-1, 1, -1000, 20, 21, 0, 19, 22, others => 0), 8),
                ( (1, 20, 0, 19, others => 0), 4));
        Tester (( (-1, -1, -1000, 22, 21, 100, 190, 22, others => 0), 8),
                ( (others => 0), 0));
    end Tester_Supprimer;


    Tab1: T_Tableau;    -- Un tableau
begin
    -- Initialiser le tableau
    Tab1 := ( (1, -4, 3, 4, 2, 52, others => 0), 6);

    -- Afficher le tableau lu
    Put ("Tableau lu : ");
    Ecrire (Tab1);
    New_Line;

    -- Supprimer toutes les éléments de Tab1
    -- TODO...

    -- Afficher le tableau Tab1
    Put ("Tableau après : ");
    Ecrire (Tab1);
    New_Line;

    Tester_Supprimer;

end Tableau_Supprimer;
