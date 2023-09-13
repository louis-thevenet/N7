with Ada.Text_IO;          use Ada.Text_IO;
with Ada.Integer_Text_IO;  use Ada.Integer_Text_IO;

-- Afficher le score du jeu 21.
--
--
-- Le jeu du 21 se joue à deux dés à 6 faces (valeurs de 1 à 6).  Chaque joueur
-- lance les dés et le gagnant est celui qui obtient le plus de points.  Ici,
-- nous ne nous intéressons qu'au calcul du score d'un lancé.
--
-- Parmi les 36 combinaisons possibles, seules les suivantes ont score non nul :
--
-- 1. Le **21** (un dé vaut 2 et l'autre 1). C'est la plus forte combinaison
--    avec un score de 21.
-- 2. Les 6 **paires** (les deux dés ont la même valeur). Le score d'une telle
--    combinaison est la somme de 10 et la valeur d'un des deux dés.  Par
--    exemple, le score de 66 est 16 (10 + 6).
-- 3. Les 5 **suites** (les valeurs des dés se suivent). Le score est alors la
--    somme des valeurs des dés.  Par exemple le score de 45 est 9.
--
-- Exemples :
--
-- de1 de2  ->  score
-- -----------------
-- 1   2    ->  21
-- 2   1    ->  21
-- 4   4    ->  14
-- 4   5    ->  9
-- 1   1    ->  11
-- 6   5    ->  11
-- 2   4    ->  0
-- 6   1    ->  0
-- 6   6    ->  16
--
procedure Score_21 is

	De1, De2 : Integer;	-- les deux dés
	Score: Integer;		-- le score obtenu avec les deux dés
begin
	-- Demander la valeur des dés
	Put ("Dé 1 : ");
	Get (De1);
	Put ("Dé 2 : ");
	Get (De2);

	-- Déterminer le score
	if De1=De2 then
        Score := 10+De1;
    elsif (De1=2 and then De2=1) or (De2=2 and then De1=1) then
        Score:=21;
    elsif De1-De2 =1 or De1-De2=-1 then
        Score:=De1+De2;
    else Score:=0;
    end if;


	-- Afficher le score
	Put ("Score : ");
	Put (Score, 1);
	New_Line;

end Score_21;
