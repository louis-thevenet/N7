with Ada.Text_IO;          use Ada.Text_IO;
with Ada.Integer_Text_IO;  use Ada.Integer_Text_IO;

-- Auteur:
-- Gérer un stock de matériel informatique.
--
package body Stocks_Materiel is

    procedure Creer (Stock : out T_Stock) is
    begin
        Stock.Nombre_Materiels:=0;
    end Creer;


    function Nb_Materiels (Stock: in T_Stock) return Integer is
    begin
        return Stock.Nombre_Materiels;
    end;


    procedure Enregistrer (
            Stock        : in out T_Stock;
            Numero_Serie : in     Integer;
            Nature       : in     T_Nature;
            Annee_Achat  : in     Integer
        ) is
        Nouveau_Materiel: T_Materiel;
    begin
        if Stock.Nombre_Materiels+1 <= CAPACITE then

            Nouveau_Materiel.Numero_Serie :=Numero_Serie;
            Nouveau_Materiel.Nature :=Nature;
            Nouveau_Materiel.Annee := Annee_Achat;
            Nouveau_Materiel.Etat:= true;
            Stock.Materiels(Stock.Nombre_Materiels+1) := Nouveau_Materiel;
            Stock.Nombre_Materiels := Stock.Nombre_Materiels+1;
        end if;
    end;


end Stocks_Materiel;
