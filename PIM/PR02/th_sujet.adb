with Ada.Text_IO;               use Ada.Text_IO;
with Ada.Integer_Text_IO;               use Ada.Integer_Text_IO;

with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Ada.Text_IO.Unbounded_IO;  use  Ada.Text_IO.Unbounded_IO;
with TH;

procedure th_sujet is

function Hachage(Cle : Unbounded_String) return Integer is
begin
    return Length(Cle);
end Hachage;


package TH_STR_INT is
    new TH (Unbounded_String, Integer, Hachage, 11);
use TH_STR_INT;

procedure Afficher_Couple (Cle : in Unbounded_String; Valeur : in Integer) is
begin
    Put("(" & Cle & " : ");
    Put(Valeur,1);
    Put(")");
    New_Line;

end Afficher_Couple;

procedure Afficher_Elements is new TH_STR_INT.Pour_Chaque(Traiter => Afficher_Couple);

Sda : T_TH;
begin
    Initialiser(Sda);
    Enregistrer(Sda, To_Unbounded_String("un"), 1);
    Enregistrer(Sda, To_Unbounded_String("deux"), 2);
    Enregistrer(Sda, To_Unbounded_String("trois"), 3);
    Enregistrer(Sda, To_Unbounded_String("quatre"), 4);
    Enregistrer(Sda, To_Unbounded_String("cinq"), 5);
    Enregistrer(Sda, To_Unbounded_String("quatre-vingt-dix-neuf"), 99);
    Enregistrer(Sda, To_Unbounded_String("vingt-et-un"), 21);

    Afficher_Elements(Sda);
    Detruire(Sda);
end th_sujet;