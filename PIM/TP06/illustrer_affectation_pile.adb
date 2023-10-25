with Piles;
with Ada.Text_IO;            use Ada.Text_IO;

-- Montrer le risque d'autoriser l'affectation entre variables dont le type
-- est une structure chaînée.
procedure Illustrer_Affectation_Pile is
	package Pile is
		new Piles (Character);
	use Pile;

	procedure Afficher is
		new Pile.Afficher (Put);

	P1, P2 : T_Pile;
begin
	-- construire la pile P1
	Initialiser (P1);
	Empiler (P1, 'A');
	Empiler (P1, 'B');
	Afficher (P1); New_Line;   -- B puis A Qu'est ce qui s'affiche ?

	P2 := P1;                  -- il vaudrait mieux copier en profondeur Conseillé ?
	pragma Assert (P1 = P2);

	Depiler (P2);              -- on dépile p1 Quel effet ?
	Afficher (P2); New_Line;   -- A Qu'est ce qui s'affiche ?
	Afficher (P1); New_Line;   -- Errur car P2 a été changé dans Dépiler Qu'est ce qui s'affiche ?
	-- XXX Que donne l'exécution avec valgrind ?

	Depiler (P1);	-- erreur correct ?
end Illustrer_Affectation_Pile;
