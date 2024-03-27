grammar Thorium;

prog: decl*;

decl: datatype
    | function
    | reactor
    ;

datatype: DATATYPE ID (enum|struct);

struct: LBRACE structMembers RBRACE ;
enum:   LBRACE enumMembers RBRACE ;

structMembers: structMember (COMMA structMember)* COMMA?;

structMember: ID COLON (enum|struct|type) ;

enumMembers: enumMember PIPE enumMember (PIPE enumMember)* ;

enumMember: ID (struct|enum| COLON type)? ;

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

reactiveType: (CONST|CELL|STREAM) type;

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

matchArgs: LPAREN ID (COMMA ID)* RPAREN;
matchCase: ID matchArgs? LTLIMPLIES expr;
matchCases: LBRACE matchCase (PIPE matchCase)* RBRACE;

expr:
      ID                         # id
    | TILDE ID                   # prev
    | expr DOT ID                # memberAccess
    | expr MATCHES ID            # streamMatches
    | MATCH expr matchCases      # match

    | op=MINUS expr              # negative
    | UNITCONST                  # unitConst
    | (TRUE|FALSE)               # bool
    | NUMBER                     # number
    | STAR expr STAR             # changes
    | LPAREN expr RPAREN         # paren
    | ID (UNITCONST|LPAREN (expr (COMMA expr)*)? RPAREN) # apply
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
TILDE      : '~' ;
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
CONST      : 'const';
MATCH      : 'match';
MATCHES    : 'matches';
FORALL     : 'forall' ;
EXISTS     : 'exists' ;
CELL       : 'cell' ;
STREAM     : 'stream' ;
DATATYPE   : 'datatype' ;
REACTOR    : 'reactor' ;
FUNCTION   : 'function' ;
PRIVATE    : 'private:' ;
PROPERTIES : 'properties:' ;
WS         : [ \r\n\t]+ -> skip ;

fragment ALPHA    : [a-zA-Z_]    ;
fragment ALPHANUM : [a-zA-Z_0-9] ;
fragment NUM : [0-9] ;

UNITCONST : '()' ;
TRUE      : 'true' ;
FALSE     : 'false' ;
ID        : ALPHA (ALPHANUM|'::')* ;
NUMBER    : NUM+ ;

COMMENT    : '/*' .*? '*/' -> skip ;
LINE_COMMENT : '//' ~[\r\n]* -> skip ;
