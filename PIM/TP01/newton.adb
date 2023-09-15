with Ada.Text_IO;          use Ada.Text_IO;
with Ada.Float_Text_IO;  use Ada.Float_Text_IO;
with Ada.Integer_Text_IO;  use Ada.Integer_Text_IO;

procedure Newton is
    Precision: Float;
    Number: Float;
    Choix: Integer;
    Ak, Ak1, Tmp: Float;
begin


	Skip_Line;
    Put("Number: ");
    Get(Number);

	Skip_Line;
    Put("Méthode différence / Méthode carré [0/1] : ");
    Get(Choix);

    if Choix=0 then
        Put("Precision: ");
        Get(Precision);

        Ak1:=1.0;
        loop
            Ak:=Ak1;
            Ak1 := (Ak + (Number / Ak)) / 2.0;
        exit when  (Ak1-Ak <= Precision);
        end loop;
    else
        Ak1:=1.0;
        loop
            Ak:=Ak1;
            Ak1 := (Ak + (Number / Ak)) / 2.0;
        exit when  (Ak1*Ak1 - Number <= Precision);
        end loop;
    end if;
    Put(Ak1);
end Newton;
