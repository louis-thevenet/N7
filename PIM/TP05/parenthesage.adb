with Ada.Text_IO; use Ada.Text_IO;
with Piles;

procedure Parenthesage is


    -- L'indice dans la chaîne Meule de l'élément Aiguille.
    -- Si l'Aiguille n'est pas dans la Meule, on retroune Meule'Last + 1.
    Function Index (Meule : in String; Aiguille: Character) return Integer with
        Post => Meule'First <= Index'Result and then Index'Result <= Meule'Last + 1
            and then (Index'Result > Meule'Last or else Meule (Index'Result) = Aiguille)
    is
    begin
        return 0;   -- TODO : à corriger !
    end Index;


    -- Programme de test de Index.
    procedure Tester_Index is
        ABCDEF : constant String := "abcdef";
    begin
        pragma Assert (1 = Index (ABCDEF, 'a'));
        pragma Assert (3 = Index (ABCDEF, 'c'));
        pragma Assert (6 = Index (ABCDEF, 'f'));
        pragma Assert (7 = Index (ABCDEF, 'z'));
        pragma Assert (4 = Index (ABCDEF (1..3), 'z'));
        pragma Assert (3 = Index (ABCDEF (3..5), 'c'));
        pragma Assert (5 = Index (ABCDEF (3..5), 'e'));
        pragma Assert (6 = Index (ABCDEF (3..5), 'a'));
        pragma Assert (6 = Index (ABCDEF (3..5), 'g'));
    end;


    -- Vérifier les bon parenthésage d'une Chaîne (D).  Le sous-programme
    -- indique si le parenthésage est bon ou non (Correct : R) et dans le cas
    -- où il n'est pas correct, l'indice (Indice_Erreur : R) du symbole qui
    -- n'est pas appairé (symbole ouvrant ou fermant).
    --
    -- Exemples
    --   "[({})]"  -> Correct
    --   "]"       -> Non Correct et Indice_Erreur = 1
    --   "((()"    -> Non Correct et Indice_Erreur = 2
    --
    procedure Verifier_Parenthesage (Chaine: in String ; Correct : out Boolean ; Indice_Erreur : out Integer) is

        function Contains(Chaine: in string; C: Character) return Integer is
        begin
            for i in Chaine'Range loop
                if Chaine(i) = C then
                    return i;
                end if;
            end loop;
            return 0;
        end Contains;


        package PPC is
            new Piles(32, Character);
        use PPC;


        Ouvrants : Constant String := "([{";
        Fermants : Constant String := ")]}";

        Pile: PPC.T_Pile;
        Caractere_Depile : Character;
        Compteur_Empile, Compteur_Depile:Integer;
        Indice_O, Indice_F:Integer;
    begin
        PPC.Initialiser(Pile);
        Compteur_Empile:=0;
        Compteur_Depile:=0;

        for i in  Chaine'Range loop
            Indice_O := Contains(Ouvrants, Chaine(i));
            Indice_F:=Contains(Fermants, Chaine(i));


            if Indice_O>0 then -- appartient à Ouvrants
                Compteur_Empile:=Compteur_Empile+1;
                PPC.Empiler(Pile, Chaine(i));


            elsif Indice_F >0 then -- appartient à Fermants
                if (PPC.Est_Vide(pile)) then
                    Correct:=false;
                    Indice_Erreur := i;
                    return;
                else
                    Caractere_Depile := PPC.Sommet(Pile);
                    if Ouvrants(Indice_F) /= Caractere_Depile then
                        Correct := false;
                        Indice_Erreur:=Compteur_Empile+1;
                        return;
                    else
                        PPC.Depiler(Pile);
                        Compteur_Empile:=Compteur_Empile-1;

                        Compteur_Depile:=Compteur_Depile+1;
                    end if;
                end if;
            end if;
        end loop;

        Indice_Erreur:=Compteur_Empile;
        Correct := PPC.Est_Vide(Pile);

    end Verifier_Parenthesage;


    -- Programme de test de Verifier_Parenthesage
    procedure Tester_Verifier_Parenthesage is
        Exemple1 : constant String(1..2) :=  "{}";
        Exemple2 : constant String(11..18) :=  "]{[(X)]}";

        Indice : Integer;   -- Résultat de ... XXX
        Correct : Boolean;
    begin
        Verifier_Parenthesage ("(a < b)", Correct, Indice);
        pragma Assert (Correct);

        Verifier_Parenthesage ("([{a}])", Correct, Indice);
        pragma Assert (Correct);

        Verifier_Parenthesage ("(][{a}])", Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 2);

        Verifier_Parenthesage ("]([{a}])", Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 1);

        Verifier_Parenthesage ("([{}])}", Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 7);

        Verifier_Parenthesage ("([{", Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 3);

        Verifier_Parenthesage ("([{}]", Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 1);

        Verifier_Parenthesage ("", Correct, Indice);
        pragma Assert (Correct);

        Verifier_Parenthesage (Exemple1, Correct, Indice);
        pragma Assert (Correct);

        Verifier_Parenthesage (Exemple2, Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 11);

        Verifier_Parenthesage (Exemple2(12..18), Correct, Indice);
        pragma Assert (Correct);
    end Tester_Verifier_Parenthesage;

begin
   --Tester_Index;
    Tester_Verifier_Parenthesage;
end Parenthesage;
