with Ada.Text_IO;          use Ada.Text_IO;

-- Permuter deux caractères lus au clavier
--
-- **Remarque :** Quand on lit un caractère, on ne consomme qu'un seul
-- caractère. Les autres caractères saisis par l'utilisateur (et en particulier
-- le retour à la ligne fait pas l'utilisateur) restent en attente d'une
-- prochaine saisie. Aussi, il faut faire un `Skip_line` pour consommer les
-- caractères restant jusqu'au prochain retour à la ligne.
--
-- Exemples :
--
-- C1 et C2 lus  -> C1 et C2 après permutation
-- -------------------------------------------
-- 'A'   'Z'     -> 'Z'   'A'
-- '0'   '!'     -> '!'   '0'
--
procedure Permuter_Caracteres is

	C1, C2, C3: Character;  -- Entier lu au clavier dont on veut connaître le signe

begin
	-- Demander les deux caractères C1 et C2
	Get (C1);
	Skip_Line;
	Get (C2);
	Skip_Line;

	-- Afficher C1
	Put_Line ("C1 = '" & C1 & "'");

	-- Afficher C2
	Put_Line ("C2 = '" & C2 & "'");

	-- Permuter C1 et C2
    C3:=C1;
    C1:=C2;
    C2:=C3;


	-- Afficher C1
	Put_Line ("C1 = '" & C1 & "'");

	-- Afficher C2
	Put_Line ("C2 = '" & C2 & "'");

end Permuter_Caracteres;
