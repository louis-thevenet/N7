with Ada.Text_IO;
use Ada.Text_IO;

-- Dans ce programme, les commentaires de spécification
-- ont **volontairement** été omis !

procedure Comprendre_Mode_Parametre is

    function Double (N : in Integer) return Integer is
    begin
        return 2 * N;
    end Double;

    procedure Incrementer (N : in out Integer) is
    begin
        N := N + 1;
    end Incrementer;

    procedure Mettre_A_Zero (N : out Integer) is
    begin
        N := 0;
    end Mettre_A_Zero;

    procedure Comprendre_Les_Contraintes_Sur_L_Appelant is
        A, B, R : Integer;
    begin
        A := 5;
        -- Indiquer pour chacune des instructions suivantes si elles sont
        -- acceptées par le compilateur.
        R := Double (A);
        R := Double (10);
        R := Double (10 * A);
        R := Double (B);

        Incrementer (A);
        Incrementer (10);     -- le paramètre doit être une variable
        Incrementer (10 * A); -- le paramètre doit être une variable
        Incrementer (B);

        Mettre_A_Zero (A);
        Mettre_A_Zero (10); -- le paramètre doit être une variable
        Mettre_A_Zero (10 * A); -- le paramètre doit être une variable
        Mettre_A_Zero (B);
    end Comprendre_Les_Contraintes_Sur_L_Appelant;


    procedure Comprendre_Les_Contrainte_Dans_Le_Corps (
            A      : in Integer;
            B1, B2 : in out Integer;
            C1, C2 : out Integer)
    is
        L: Integer;
    begin
        -- pour chaque affectation suivante indiquer si elle est autorisée
        L := A; --oui
        A := 1; -- non

        B1 := 5; --oui

        L := B2; -- oui
        B2 := B2 + 1; --oui

        C1 := L; --oui

        L := C2; -- non

        C2 := A; -- oui
        C2 := C2 + 1; -- oui
    end Comprendre_Les_Contrainte_Dans_Le_Corps;


begin
    Comprendre_Les_Contraintes_Sur_L_Appelant;
    Put_Line ("Fin");
end Comprendre_Mode_Parametre;
