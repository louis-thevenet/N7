with Ada.Text_IO;               use Ada.Text_IO;
with Ada.Integer_Text_IO;               use Ada.Integer_Text_IO;

with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Ada.Text_IO.Unbounded_IO;  use  Ada.Text_IO.Unbounded_IO;
with LCA;

procedure lca_sujet is

package LCA_STR_INT is
    new LCA (Unbounded_String, Integer);
use LCA_STR_INT;

procedure Afficher_Couple (Cle : in Unbounded_String; Valeur : in Integer) is
begin
    Put("[" & Cle & ":");
    Put(Valeur,1);
    Put("] --> ");

end Afficher_Couple;

procedure Afficher_Elements is new LCA_STR_INT.Pour_Chaque(Traiter => Afficher_Couple);

Sda : T_LCA;
begin
    Initialiser(Sda);
    Enregistrer(Sda, To_Unbounded_String("un"), 1);
    Enregistrer(Sda, To_Unbounded_String("deux"), 2);
    Afficher_Elements(Sda);
    Detruire(Sda);
end lca_sujet;