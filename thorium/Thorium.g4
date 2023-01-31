grammar Thorium;

prog: decl*;

decl: struct
    | enum
    | function
    | reactor
    ;

struct: STRUCT ID LBRACE structMembers? RBRACE ;

enum:     ENUM ID LBRACE enumMembers? RBRACE ;

function: FUNCTION ID LPAREN functionParams? RPAREN '->' type LBRACE
    functionProperties?
RBRACE;

functionParams: functionParam (COMMA functionParam)* ;

functionParam: ID COLON type;

functionProperties: functionProperty (SEMI functionProperty)* SEMI? ;

functionProperty: expr;

reactor: REACTOR ID reactorParams? LBRACE 
    reactorMembers?
(PRIVATE
    reactorMembers?)?
(PROPERTIES
    reactorProperties?)?
RBRACE ;

reactorParams: LPAREN reactorParam (COMMA reactorParam)* RPAREN;

reactorParam: ID COLON reactiveType;

reactorMembers: reactorMember (SEMI reactorMember)* SEMI?;

reactorMember: ID COLON reactiveType EQUALS expr;

reactorProperties: reactorProperty (SEMI reactorProperty)* SEMI?;

reactorProperty: ID COLON property;

structMembers: structMember (COMMA structMember)* COMMA?;

structMember: ID COLON type ;

enumMembers: enumMember (COMMA enumMember)* ;

enumMember: ID COLON type ;

enumParams: type (COMMA type)* ;

reactiveType: (CELL|STREAM) type;

type : ID ;

property:
          ltlProperty
//        | quantProperty
        ;

ltlProperty:
      NOT ltlProperty                               # ltlNegation
    | LPAREN ltlProperty RPAREN                     # ltlParen
    | NEXT ltlProperty                              # ltlNext
    | GLOBALLY ltlProperty                          # ltlGlobally
    | HISTORICALLY ltlProperty                      # ltlHistorically
    | EVENTUALLY ltlProperty                        # ltlEventually
    | PREVIOUSLY ltlProperty                        # ltlPreviously
    | ltlProperty UNTIL ltlProperty                 # ltlUntil
    | ltlProperty SINCE ltlProperty                 # ltlSince
    | <assoc=right> ltlProperty AND ltlProperty     # ltlAnd
    | <assoc=right> ltlProperty OR ltlProperty      # ltlOr
    | <assoc=right> ltlProperty (LTLIMPLIES|IMPLIES) ltlProperty # ltlImplication
    | expr                                          # ltlExpr
    ;

//quantProperty:
//      FORALL ID (COMMA ID)* quantProperty # forall
//      EXISTS ID (COMMA ID)* quantProperty # exists
//    | expr
//    ;

expr:
      expr DOT ID                # memberAccess
    | op=MINUS expr              # negative
    | UNIT                       # unit
    | (TRUE|FALSE)               # bool
    | ID                         # id
    | NUMBER                     # number
    | STAR expr STAR             # changes
    | LPAREN expr RPAREN         # paren
    | ID LPAREN expr (COMMA expr)* RPAREN # apply
    | expr op=(STAR|DIV) expr    # mult
    | expr op=(PLUS|MINUS) expr  # add
    | expr op=(LT|LE|GT|GE) expr # compare
    | expr op=(EQ|NEQ) expr      # equals
    | op=NOT expr                # not
    | expr op=AND expr           # and
    | expr op=OR  expr           # or
    | <assoc=right> expr op=IMPLIES expr # implication
    | expr AT expr               # snapshot
    | <assoc=right> expr IF expr   # filter
    | <assoc=right> expr PIPE expr # merge
    | expr DOTS expr               # hold
    ;

LPAREN     : '(' ;
RPAREN     : ')' ;
LBRACKET   : '[' ;
RBRACKET   : ']' ;
LBRACE     : '{' ;
RBRACE     : '}' ;
EQUALS     : '=' ;
COLON      : ':' ;
SEMI       : ';' ;
COMMA      : ',' ;
DOT        : '.' ;
DOTS       : '..' ;
PLUS       : '+' ;
MINUS      : '-' ;
STAR       : '*' ;
DIV        : '/' ;
LT         : '<' ;
LE         : '<=' ;
GT         : '>' ;
GE         : '>=' ;
EQ         : '==' ;
NEQ        : '!=' ;
AND        : 'and' ;
OR         : 'or' ;
PIPE       : '|' ;
IF         : 'if' ;
AT         : '@' ;
NOT        : 'not' ;
NEXT       : 'X' ;
GLOBALLY   : 'G' ;
HISTORICALLY : 'H' ;
EVENTUALLY : 'F' ;
PREVIOUSLY : 'P' ;
UNTIL      : 'U' ;
SINCE      : 'S' ;
IMPLIES    : '->' ;
LTLIMPLIES : '=>' ;
FORALL     : 'forall' ;
EXISTS     : 'exists' ;
CELL       : 'cell' ;
STREAM     : 'stream' ;
STRUCT     : 'struct' ;
ENUM       : 'enum' ;
REACTOR    : 'reactor' ;
FUNCTION   : 'function' ;
PRIVATE    : 'private:' ;
PROPERTIES : 'properties:' ;
WS         : [ \r\n\t]+ -> skip ;

fragment ALPHA    : [a-zA-Z_]    ;
fragment ALPHANUM : [a-zA-Z_0-9] ;
fragment NUM : [0-9] ;

UNIT   : '()' ;
TRUE   : 'true' ;
FALSE  : 'false' ;
ID : ALPHA ALPHANUM* ;
NUMBER : NUM+ ;

COMMENT    : '/*' .*? '*/' -> skip ;
LINE_COMMENT : '//' ~[\r\n]* -> skip ;
