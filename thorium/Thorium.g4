grammar Thorium;

prog: decl*;

decl: struct
    | enum
    | reactor
    ;

struct: STRUCT ID LBRACE structMembers? RBRACE ;

enum:     ENUM ID LBRACE enumMembers? RBRACE ;

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

reactorProperties: expr (SEMI expr)* ;

structMembers: structMember (COMMA structMember)* ;

structMember: ID COLON type ;

enumMembers: enumMember (COMMA enumMember)* ;
enumMember: ID COLON type ;

enumParams: type (COMMA type)* ;

reactiveType: (CELL|STREAM) type;

type : ID ;

expr:
      MINUS expr              # negative
    | ID                      # id
    | NUMBER                  # number
    | LPAREN expr RPAREN      # paren
    | expr op=(STAR|DIV) expr    # mult
    | expr op=(PLUS|MINUS) expr  # add
    | expr op=(LT|LE|GT|GE) expr # compare
    | expr op=(EQ|NEQ) expr      # equals
    | expr op=AND expr           # and
    | expr op=OR  expr           # or
    | expr AT expr            # snapshot
    | <assoc=right> expr PIPE expr          # alternate
    | <assoc=right> expr IF expr          # filter
    | expr DOTS expr          # hold
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
CELL       : 'cell' ;
STREAM     : 'stream' ;
STRUCT     : 'struct' ;
ENUM       : 'enum' ;
REACTOR    : 'reactor' ;
PRIVATE    : 'private:' ;
PROPERTIES : 'properties:' ;
WS         : [ \r\n\t]+ -> skip;

fragment ALPHA    : [a-zA-Z_]    ;
fragment ALPHANUM : [a-zA-Z_0-9] ;
fragment NUM : [0-9] ;

ID : ALPHA ALPHANUM* ;
NUMBER : NUM+ ;
