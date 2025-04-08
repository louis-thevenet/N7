lexer grammar MiniCLexer;

@header {
package fr.n7.stl.minic.parser;
}

Egal: '=';
AccoladeOuvrante: '{';
AccoladeFermante: '}';
ParentheseOuvrante: '(';
ParentheseFermante: ')';
CrochetOuvrant: '[';
CrochetFermant:']';
Point: '.';
PointInterrogation: '?';
DeuxPoint: ':';
Virgule: ',';
PointVirgule: ';';
Afficher: 'print';
Si: 'if';
TantQue: 'while';
Sinon: 'else';
Retour: 'return';
DefinitionConstante: 'const';
DefinitionType: 'typedef';
Enregistrement: 'struct';
Enumeration: 'enum';
Nouveau: 'new';

// Operateurs
// Par défaut, les opérateurs sont associatifs à gauche
Asterisque: '*';
Oblique: '/';
PourCent: '%';
Plus: '+';
Moins: '-';
// Operateurs logiques
DoubleBarre: '||';
DoubleEsperluette: '&&';
PointExclamation: '!';
// Operateurs de comparaison
Inferieur: '<';
Superieur: '>';
InferieurEgal: '<=';
SuperieurEgal: '>=';
DoubleEgal: '==';
ExclamationEgal: '!=';
Esperluette: '&';
// Types
TypeEntier: 'int';
TypeFlottant: 'float';
TypeBooleen: 'boolean';
TypeCaractere: 'char';
TypeChaine: 'String';
TypeVide: 'void';

Vrai: 'true';
Faux: 'false';
Nul: 'null';
Premier: 'fst';
Second: 'snd';
Caractere: '\'' . '\'';
Chaine: '"' .*? '"';

Identificateur: [a-zA-Z][a-zA-Z_0-9]*;
Entier: '0' | ([1-9][0-9]*);
Flottant: Entier '.' Entier;

// Commentaires de ligne
CommentaireLigne: '//' ~[\r\n]* -> skip;

// Commentaires de bloc
CommentaireBloc: '/*' .*? '*/' -> skip;

// Blancs
WS: [ \t\r\n]+ -> skip;
