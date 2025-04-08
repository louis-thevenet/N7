parser grammar MiniCParser;
options { tokenVocab=MiniCLexer; }

@header {
package fr.n7.stl.minic.parser;
import java.io.IOException;
import java.io.File;
import java.io.FileInputStream;
import java.io.PrintWriter;
import java.io.IOException;
import fr.n7.stl.minic.ast.*;
import fr.n7.stl.minic.ast.expression.*;
import fr.n7.stl.minic.ast.expression.accessible.*;
import fr.n7.stl.minic.ast.expression.allocation.*;
import fr.n7.stl.minic.ast.expression.assignable.*;
import fr.n7.stl.minic.ast.expression.value.*;
import fr.n7.stl.minic.ast.instruction.*;
import fr.n7.stl.minic.ast.instruction.declaration.*;
import fr.n7.stl.minic.ast.scope.*;
import fr.n7.stl.minic.ast.type.*;
import fr.n7.stl.minic.ast.type.declaration.*;
import fr.n7.stl.util.*;
import fr.n7.stl.tam.ast.*;
import fr.n7.stl.tam.ast.impl.*;
}

programme : name=Identificateur main=bloc;

bloc returns [Block b]: AccoladeOuvrante instructions += instruction* AccoladeFermante;

// Liste de declarations de paramètres séparées par une virgule, peut être vide.
parametres returns [List<ParameterDeclaration> l]:
    /* vide */ 
    | 
    type1=type ident1=identifiant (Virgule suiteType+=type suiteIdent+=identifiant)*
;

instruction returns [Instruction i]: 
    (DefinitionConstante | /* vide */) type identifiant Egal expression PointVirgule #instructionDeclaration
    | DefinitionType type identifiant PointVirgule #instructionTypeDeclaration
    | type identifiant ParentheseOuvrante parametres ParentheseFermante bloc #instructionFunctionDeclaration
    | affectable Egal valeur=expression PointVirgule #instructionAffectation
    | Afficher expression PointVirgule #instructionAffichage
    | Si ParentheseOuvrante expression ParentheseFermante alors=bloc #instructionSi
    | Si ParentheseOuvrante expression ParentheseFermante alors=bloc Sinon sinon=bloc #instructionSiSinon
    | Retour expression PointVirgule #instructionReturn
    | TantQue ParentheseOuvrante expression ParentheseFermante corps=bloc #instructionTantQue
;

atomique returns [AtomicType t]:
    TypeEntier
    | TypeFlottant
    | TypeBooleen
    | TypeCaractere
    | TypeChaine
    | TypeVide
;

champ returns [FieldDeclaration f]:
    type identifiant PointVirgule;

// Liste d'etiquettes séparées par une virgule, ne peut pas être vide
etiquettes returns [List<LabelDeclaration> l]:
    premiere=Identificateur (Virgule suite+=Identificateur)*
;

type returns [Type t]:
    atomique #typeAtomic
    | Identificateur #typeNamed
    | Inferieur gauche=type Virgule droite=type Superieur #typeCouple
    | Enregistrement Identificateur AccoladeOuvrante champs+=champ+ AccoladeFermante #typeRecord
    | Enumeration Identificateur AccoladeOuvrante etiquettes AccoladeFermante #typeEnum
;

affectable returns [AssignableExpression a]:
    ident=Identificateur  #affectableIdentifiant
    | Asterisque expression #affectablePointer
    | affectable CrochetOuvrant expression CrochetFermant #affectableArray
    | ParentheseOuvrante (Identificateur | atomique) ParentheseFermante affectable #affectableConversion
    | affectable Point Identificateur #affectableField
;

// Liste d'expressions séparées par une virgule, ne peut pas être vide
expressions returns [List<AccessibleExpression> l]:
    premiere=expression (Virgule suite+=expression)*;

// Liste d'expressions séparées par une virgule, peut être vide
arguments returns [List<AccessibleExpression> l]:
    /* Vide */ 
    | expressions 
;

// Les expressions vont du plus prioritaire (en haut) au moins prioritaire (en bas).
expression returns [AccessibleExpression e]:
    ParentheseOuvrante expression ParentheseFermante #expressionParenthese
    | expression Point Identificateur #expressionField
    | tableau=expression CrochetOuvrant indice=expression CrochetFermant #expressionArrayAcess
    | PointExclamation expr=expression #expressionNot
    | Premier expression #expressionFirst
    | Second expression #expressionSecond
    | Moins expression #expressionOpposite 
    | Nouveau type CrochetOuvrant expression CrochetFermant #expressionArrayAllocation
    | Nouveau type ParentheseOuvrante ParentheseFermante #expressionPointerAllocation
    | gauche=expression op=(Asterisque | Oblique | PourCent) droite=expression #expressionMultiplicative
    | gauche=expression op=(Plus | Moins) droite=expression #expressionAdditive
    | gauche=expression op=(Inferieur | InferieurEgal | Superieur | SuperieurEgal) droite=expression #expressionInequality
    | gauche=expression op=(DoubleEgal | ExclamationEgal) droite=expression #expressionEquality
    | gauche=expression DoubleEsperluette droite=expression #expressionAnd
    | gauche=expression DoubleBarre droite=expression #expressionOr
    | condition=expression PointInterrogation alors=expression DeuxPoint sinon=expression #expressionConditional
    | AccoladeOuvrante expressions AccoladeFermante #expressionSequence
    | Inferieur gauche=expression Virgule droite=expression Superieur #expressionCouple
    | Identificateur ParentheseOuvrante arguments ParentheseFermante #expressionFunctionCall
    | Asterisque expression #expressionPointerAccess
    | Esperluette affectable #expressionAddress
    | ParentheseOuvrante (Identificateur | atomique) ParentheseFermante expression #expressionConversion
    | Vrai #expressionTrue
    | Faux #expressionFalse
    | Entier #expressionInt
    | Flottant #expresionFloat
    | Caractere #expressionCharacter
    | Chaine #expressionString
    | Nul #expressionNull
    | Identificateur #expressionAccess

;


identifiant returns [fr.n7.stl.util.Pair<String, PartialType> id] :
    identifiant CrochetOuvrant CrochetFermant
    | Asterisque identifiant
    | ParentheseOuvrante identifiant ParentheseFermante
    | Identificateur
;