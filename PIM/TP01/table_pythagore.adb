with Ada.Text_IO;          use Ada.Text_IO;
with Ada.Integer_Text_IO;  use Ada.Integer_Text_IO;

-- Afficher la table de Pythagore
--
-- Exemple : Taille = 3
--
-- X  1  2  3
-- 1  1  2  3
-- 2  2  4  6
-- 3  3  6  9
--
-- Exemple : Taille = 9
--
-- X  1  2  3  4  5  6  7  8  9
-- 1  1  2  3  4  5  6  7  8  9
-- 2  2  4  6  8 10 12 14 16 18
-- 3  3  6  9 12 15 18 21 24 27
-- 4  4  8 12 16 20 24 28 32 36
-- 5  5 10 15 20 25 30 35 40 45
-- 6  6 12 18 24 30 36 42 48 54
-- 7  7 14 21 28 35 42 49 56 63
-- 8  8 16 24 32 40 48 56 64 72
-- 9  9 18 27 36 45 54 63 72 81
--
procedure Table_Pythagore is

	Taille: Integer;	-- taille de la table
begin
	-- Demander la taille
	Put ("Taille de la table : ");
	Get (Taille);

	-- Afficher la table de Pythagore
	for i in 1..9 loop
        for j in 1..9 loop
            Put(j*i);
        end loop;
       	New_Line;

    end loop;

end Table_Pythagore;
