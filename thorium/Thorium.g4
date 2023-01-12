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

expr: expr DOTS expr          # hold
    | expr AT expr            # snapshot
    | expr (PLUS|MINUS) expr  # add
    | expr (STAR|DIV) expr    # mult
    | MINUS expr              # negative
    | ID                      # id
    | NUMBER                  # number
    | LPAREN expr RPAREN      # paren
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
