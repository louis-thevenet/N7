with Ada.Text_IO;          use Ada.Text_IO;
with Ada.Float_Text_IO;  use Ada.Float_Text_IO;

procedure Newton is
    Precision: Float;
    Number: Float;
    Ak, Ak1, Tmp: Float;
begin
    Put("Precision: ");
    Get(Precision);
	Skip_Line;

    Put("Number: ");
    Get(Number);

    Ak1:=1.0;
    loop
        Ak:=Ak1;
        Ak1 := (Ak + (Number / Ak)) / 2.0;
    exit when  (Ak1-Ak <= Precision);
    end loop;

    Put(Ak1);
end Newton;
