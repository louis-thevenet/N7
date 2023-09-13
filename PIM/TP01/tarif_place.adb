with Ada.Text_IO;          use Ada.Text_IO;
with Ada.Integer_Text_IO;  use Ada.Integer_Text_IO;
with Ada.Float_Text_IO;    use Ada.Float_Text_IO;

-- Afficher le tarif d'une place
--
-- Le tarif normal de la place est de 12,60 €. Les enfants (moins de 14 ans)
-- paient 7 €. Les séniors (65 ans et plus) paient 10,30 €.
--
-- Exemples :
--
--   age  ->  tarif
--   -----------------
--   25   ->  12.60
--    8   ->  7.0
--   75   ->  10.30
--   14   ->  12.60
--
procedure Tarif_Place is

	Age: Integer;  -- l'âge de la personne
	Tarif: Float;  -- le tarif à appliquer
begin
	-- Demander l'age
	Put ("Âge : ");
	Get (Age);

	-- Déterminer le tarif de la place
	case Age is
        when 1..14 => Tarif:=7.0;
        when 15..64 => Tarif:=12.60;
        when others=>Tarif:=10.3;
    end case;

	-- Afficher le tarif
	Put ("Le tarif pour ");
	Put (Age, 1);
	Put (" ans est ");
	Put (Tarif, Exp => 0, Aft => 2, Fore => 1);
	Put (" euros.");
	New_Line;

end Tarif_Place;
