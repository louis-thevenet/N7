with Text_Io;              use Text_Io;
with Ada.Integer_Text_Io;  use Ada.Integer_Text_Io;
with Alea;
with Jeu_Devin_Exo1;
with Jeu_Devin_Exo2;

-- Auteur : Louis THEVENET
procedure Jeu_Devin_Exo3 is
-- Jouer au jeu du devin dans le rôle souhaité
procedure Afficher_Menu is
begin
	New_Line;
	Put("1- L'ordinateur choisit un nombre et vous le devinez");
	New_Line;
	Put("2- Vous choisissez un nombre et l'ordinateur le devine");
	New_Line;
	Put("0- Quitter le programme");
	new_Line;
	Put("Votre choix : ");
end Afficher_Menu;

Choix: Integer;
begin
	while true loop
		Afficher_Menu;
		Get(Choix);
		New_Line;
		case Choix is
			when 0 => 
				Put("Au revoir...");
				return;
			when 1 => Jeu_Devin_Exo1;
			when 2 => Jeu_Devin_Exo2;
			when others => 
				New_Line;
				Put("Choix incorrect.");
		end case;
	end loop;
end Jeu_Devin_Exo3;
