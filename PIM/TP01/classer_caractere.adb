with Ada.Text_IO;          use Ada.Text_IO;

-- afficher la classe à laquelle appartient un caractère lu au clavier
--
-- La classe d'un caractère peut-être 'C' pour Chiffre, 'L' pour Lettre, 'P'
-- pour Ponctuation ou 'A' pour Autre.
--
--  Exemples :
--
--  c    ->  classe
-- -------------------
-- '4'   ->  'C'
-- 'A'   ->  'L'
-- 'd'   ->  'L'
-- '!'   ->  'P'
-- '<'   ->  'A'
-- '='   ->  'A'
-- ','   ->  'P'
-- ';'   ->  'P'
-- '.'   ->  'P'
-- '?'   ->  'P'
-- 'z'   ->  'L'
-- 'Z'   ->  'L'
-- 'a'   ->  'L'
-- '0'   ->  'C'
-- '9'   ->  'C'
-- 'à'   ->  'A'
-- 'Ü'   ->  'A'
--
procedure Classer_Caractere is

	-- Constantes pour définir la classe des caractères
	--   Remarque : Dans la suite du cours nous verrons une meilleure
	--   façon de faire que de définir ces constantes.  Laquelle ?
	Chiffre     : constant Character := 'C';
	Lettre      : constant Character := 'L';
	Ponctuation : constant Character := 'P';
	Autre       : constant Character := 'A';

	C : Character;		-- le caractère à classer
	Classe: Character;	-- la classe du caractère C
begin
	-- Demander le caractère
	Put ("Caractère : ");
	Get (C);

	-- Déterminer la classe du caractère c

	case c is
        when 'a'..'z' | 'A'..'Z'=> Classe := Lettre;
        when '0'..'9' => Classe := Chiffre;
        when ';' | ',' | ':'|'.'|'?' => Classe := Ponctuation;
        when others => Classe := Autre;
    end case;

	-- Afficher la classe du caractère
	Put_Line ("Classe : " & Classe);

end Classer_Caractere;
