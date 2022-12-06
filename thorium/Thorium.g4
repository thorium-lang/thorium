grammar Thorium;

prog: decl*;

decl: struct
    | enum
    ;

struct: STRUCT ID LBRACE structMembers? RBRACE ;

enum:     ENUM ID LBRACE enumMembers? RBRACE ;

structMembers: structMember (COMMA structMember)* ;

structMember: ID COLON type ;

enumMembers: enumMember (COMMA enumMember)* ;

enumMember: ID (LPAREN enumParams RPAREN)? ;

enumParams: type (COMMA type)* ;

type : ID ;


LPAREN   : '(' ;
RPAREN   : ')' ;
LBRACKET : '[' ;
RBRACKET : ']' ;
LBRACE   : '{' ;
RBRACE   : '}' ;
COLON    : ':' ;
COMMA    : ',' ;
STRUCT   : 'struct' ;
ENUM     : 'enum' ;
WS       : [ \r\n\t]+ -> skip;

fragment ALPHA    : [a-zA-Z_]    ;
fragment ALPHANUM : [a-zA-Z_0-9] ;

ID : ALPHA ALPHANUM* ;
