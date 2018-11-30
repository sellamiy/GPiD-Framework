/* ----------------------------------------------------- */
/* ----------------------- WhyML ----------------------- */
/* ----------------------------------------------------- */
grammar WhyML;
/* ----------------------------------------------------- */
/* ----------------------- Parser ---------------------- */
/* ----------------------------------------------------- */
// Lexical wrappers
op
    : (EQUAL | LOWER | GREATER
        | TILDA | PLUS | MINUS | STAR | SLASH | PERCENT
        | EXCLAM | DOLLAR | AMPER | QMARK | ATSYM | CAP | DOT | COLUMN | VBAR | SHARP
        | MULTIOP) SQUOTE*;

qualifier : (uident DOT)+ ;
lqualid : qualifier? lident ;
uqualid : qualifier? uident ;

ident : lident | uident ;

attribute : ATTRIBUTE | LOCATION ;
// Wrappers
label : attribute ;
lident_nq : lident ;
uident_nq : uident ;
ident_nq : ident ;

integer : INTEGER ;
real : REAL ;
boolean : TRUE | FALSE ;

lident : LIDENT ;
uident : UIDENT ;
/* ----------------------------------------------------- */
// Type expressions
type
    : lqualid type_arg+
    | type RIGHTARROW type
    | type_arg
    ;

type_arg
    : lqualid
    | QIDENT
    | OPAR CPAR
    | OPAR type (COMMA type)+ CPAR
    | OCURLY type CCURLY
    | qualifier? OPAR type CPAR
    ;
/* ----------------------------------------------------- */
// Logical expressions
term
    : integer
    | real
    | boolean
    | OPAR CPAR
    | qualid
    | qualifier? OPAR term CPAR
    | qualifier? BEGIN term END
    | op term
    | term op term
    | OCURLY term_field+ CCURLY
    | OCURLY term WITH term_field+ CCURLY
    | term DOT lqualid
    | term OBRACKET term CBRACKET SQUOTE*
    | term OBRACKET term LEFTARROW term CBRACKET SQUOTE*
    | term OBRACKET term DOT DOT term CBRACKET SQUOTE*
    | term OBRACKET DOT DOT term CBRACKET SQUOTE*
    | term OBRACKET term DOT DOT CBRACKET SQUOTE*
    | term term+
    | term AT uident
    | AT term SQUOTE uident // 6.6.1 addition
    | OLD term
    // Second part of terms
    | NOT term
    | term LOG_AND term
    | term PRG_AND term
    | term LOG_OR term
    | term PRG_OR term
    | term BY term
    | term SO term
    | term RIGHTARROW term
    | term EQUIV term
    | term COLUMN type
    | attribute+ term
    | term (COMMA term)+
    | QUANTIFIER quant_vars triggers? DOT term
    // Third part of terms
    | IF term THEN term ELSE term
    | MATCH term WITH term_case+ END
    | LET pattern EQUAL term IN term
    | LET symbol param+ EQUAL term IN term
    | FUN param+ RIGHTARROW term
    ;

term_field : lqualid EQUAL term SEMICOLUMN ;

qualid : qualifier? (lident_ext | uident) ;

lident_ext : lident
    | OPAR ident_op CPAR
    | OPAR ident_op CPAR (VBAR | SQUOTE) uident // Warning : Not conform
    ;

ident_op
    : op
    | op UNDERSCORE
    | OBRACKET CBRACKET SQUOTE*
    | OBRACKET LEFTARROW CBRACKET SQUOTE*
    | OBRACKET CBRACKET SQUOTE* LEFTARROW
    | OBRACKET DOT DOT CBRACKET SQUOTE*
    | OBRACKET UNDERSCORE DOT DOT CBRACKET SQUOTE*
    | OBRACKET DOT DOT UNDERSCORE CBRACKET SQUOTE*
    ;

quant_vars : quant_cast (COMMA quant_cast)* ;

quant_cast : binder+ (COLUMN type)? ;

binder : UNDERSCORE | bound_var ;

bound_var : lident attribute* ;

triggers : OBRACKET trigger (VBAR trigger)* CBRACKET ;

trigger : term (COMMA term)* ;

term_case : VBAR pattern RIGHTARROW term ;

pattern
    : binder
    | OPAR CPAR
    | OCURLY (lqualid EQUAL pattern SEMICOLUMN)+ CCURLY
    | uqualid pattern*
    | GHOST pattern
    | pattern AS GHOST? bound_var
    | pattern COMMA pattern
    | pattern VBAR pattern
    | qualifier? OPAR pattern CPAR
    ;

symbol : lident_ext attribute* ;

param
    : type_arg
    | binder
    | OPAR GHOST? type CPAR
    | OPAR GHOST? binder CPAR
    | OPAR GHOST? binder+ COLUMN type CPAR
    ;
/* ----------------------------------------------------- */
// Program expressions
expr
    : integer
    | real
    | boolean
    | OPAR CPAR
    | qualid
    | expr_r_parentheses
    | qualifier? BEGIN expr END
    | op expr
    | OCURLY (lqualid EQUAL expr SEMICOLUMN)+ CCURLY
    | OCURLY expr WITH (lqualid EQUAL expr SEMICOLUMN)+ CCURLY
    | expr DOT lqualid
    | expr OBRACKET expr CBRACKET SQUOTE*
    | expr OBRACKET expr LEFTARROW expr CBRACKET SQUOTE*
    | expr OBRACKET expr DOT DOT expr CBRACKET SQUOTE*
    | expr OBRACKET expr DOT DOT CBRACKET SQUOTE*
    | expr OBRACKET DOT DOT expr CBRACKET SQUOTE*
    | expr expr+ ww_application
    | expr op expr
    | NOT expr
    | expr PRG_AND expr
    | expr PRG_OR expr
    | expr COLUMN expr
    | attribute+ expr
    | GHOST expr
    | expr (COMMA expr)+
    | expr LEFTARROW expr
    // Second part of expressions
    | expr spec+
    | IF expr THEN expr (ELSE expr)?
    | MATCH expr WITH (VBAR pattern RIGHTARROW expr)+ END
    | qualifier? BEGIN spec+ expr END
    | expr SEMICOLUMN expr
    | expr_r_letpattern
    | LET fun_defn IN expr
    | LET REC fun_defn (WITH fun_defn)* IN expr
    | FUN param+ spec* RIGHTARROW spec* expr
    | ANY result spec*
    // Wrapping part of expressions
    | LOOP invariant* variant? expr END
    | WHILE expr DO invariant* variant? expr DONE
    | expr_r_forloop
    | assertion
    | RAISE uqualid
    | RAISE OPAR uqualid expr CPAR
    | TRY expr WITH (VBAR handler)+ END
    // Unsafe wraps
    | expr SEMICOLUMN
    ;

fun_defn : fun_head spec* EQUAL spec* expr ;

fun_head : GHOST? kind? symbol param+ (COLUMN result)? ;

kind : FUNCTION | PREDICATE | LEMMA ;

result
    : ret_type
    | OPAR ret_type (COMMA ret_type)* CPAR
    | OPAR ret_name (COMMA ret_name)* CPAR
    ;

ret_type : GHOST? type ;

ret_name : GHOST? binder COLUMN type ;

spec
    : REQUIRES OCURLY term CCURLY
    | ENSURES OCURLY term CCURLY
    | RETURNS OCURLY (VBAR pattern RIGHTARROW term)+ CCURLY
    | RAISES OCURLY (VBAR pattern RIGHTARROW term)+ CCURLY
    | RAISES OCURLY uqualid (COMMA uqualid)* CCURLY
    | READS OCURLY lqualid (COMMA lqualid)* CCURLY
    | WRITES OCURLY path (COMMA path)* CCURLY
    | ALIAS OCURLY alias (COMMA alias)* CCURLY
    | VARIANT OCURLY variant (COMMA variant)* CCURLY
    | DIVERGES
    | (READS | WRITES | ALIAS) OCURLY CCURLY
    ;

path : lqualid (DOT lqualid)* ;

alias : path WITH path ;

variant : term (WITH lqualid)? ;

// Wrappers

expr_r_parentheses : qualifier? OPAR expr CPAR ;

expr_r_letpattern : LET pattern EQUAL expr IN expr ;

expr_r_forloop : FOR lident EQUAL expr (TO | DOWNTO) expr DO invariant* expr DONE ;

// Wrap handlers
ww_application : ;
/* ----------------------------------------------------- */
// Why3 formulas
formula
    : boolean
    | formula RIGHTARROW formula
    | formula EQUIV formula
    | formula LOG_AND formula
    | formula PRG_AND formula
    | formula LOG_OR formula
    | formula PRG_OR formula
    | formula BY formula
    | formula SO formula
    | NOT formula
    | lqualid
    | op term
    | term op term
    | lqualid term+
    | IF formula THEN formula ELSE formula
    | LET pattern EQUAL term IN formula
    | MATCH term (COMMA term)+ WITH (VBAR formula_case)+ END
    | QUANTIFIER binders (COMMA binders)* form_triggers? DOT formula
    | label formula
    | OPAR formula CPAR
    ;

binders : lident+ COLUMN type ;

form_triggers : OBRACKET form_trigger (VBAR form_trigger)* CBRACKET ; // Wrap (extend)

form_trigger : tr_term (COMMA tr_term)* ; // Wrap (extend)

tr_term : term | formula ;

formula_case : pattern RIGHTARROW formula ;
/* ----------------------------------------------------- */
// Why3 theories
theory : THEORY uident_nq label* decl* END ;

decl
    : TYPE type_decl (WITH type_decl)*
    | CONSTANT constant_decl
    | FUNCTION function_decl (WITH logic_decl)*
    | PREDICATE predicate_decl (WITH logic_decl)*
    | INDUCTIVE inductive_decl (WITH inductive_decl)*
    | COINDUCTIVE inductive_decl (WITH inductive_decl)*
    | AXIOM ident_nq COLUMN formula
    | LEMMA ident_nq COLUMN formula
    | GOAL ident_nq COLUMN formula
    | USE imp_exp tqualid (AS uident)?
    | CLONE  imp_exp tqualid (AS uident)? subst?
    | NAMESPACE IMPORT? uident_nq decl* END
    ;

logic_decl : function_decl | predicate_decl ;

constant_decl
    : lident_nq label* COLUMN type
    | lident_nq label* COLUMN type EQUAL term
    ;

function_decl
    : lident_nq label* type_param* COLUMN type
    | lident_nq label* type_param* COLUMN type EQUAL term
    ;

predicate_decl
    : lident_nq label* type_param*
    | lident_nq label* type_param* EQUAL formula
    ;

inductive_decl : lident_nq label* type_param* EQUAL VBAR? ind_case (VBAR ind_case)* ;

ind_case : ident_nq label* COLUMN formula ;

imp_exp : (IMPORT | EXPORT)? ;

subst : WITH (COMMA subst_elt)+ ;

subst_elt
    : TYPE lqualid EQUAL lqualid
    | FUNCTION lqualid EQUAL lqualid
    | PREDICATE lqualid EQUAL lqualid
    | NAMESPACE (uqualid | DOT) EQUAL (uqualid | DOT)
    | LEMMA qualid
    | GOAL qualid
    ;

tqualid : uident | ident (DOT ident)* DOT uident ;

type_decl : lident_nq label* (SQUOTE lident_nq label*)* type_defn ;

type_defn : // Empty
    | EQUAL type
    | EQUAL VBAR? type_case (VBAR type_case)*
    | EQUAL OCURLY record_field (SEMICOLUMN record_field)* CCURLY
    | LOWER RANGE integer integer GREATER
    | LOWER FLOAT_KW integer integer GREATER
    ;

type_case : uident label* type_param* ;

record_field : lident label* COLUMN type ;

type_param
    : SQUOTE lident
    | lqualid
    | OPAR lident+ COLUMN type CPAR
    | OPAR type (COMMA type)* CPAR
    | OPAR CPAR
    ;
/* ----------------------------------------------------- */
// WhyML specs
/*
spec : requires | ensures | returns_rule | raises | reads | writes | variant ;

requires : REQUIRES OCURLY formula CCURLY ;

ensures : ENSURES OCURLY formula CCURLY ;

returns_rule : RETURNS OCURLY VBAR? formula_case (VBAR formula_case)* CCURLY ;

reads : READS OCURLY term (COMMA term)* CCURLY ;

writes : WRITES OCURLY term (COMMA term)* CCURLY ;

raises : RAISES OCURLY VBAR? raises_case (VBAR raises_case)* CCURLY
    | RAISES OCURLY uqualid (COMMA uqualid)* CCURLY ;

raises_case : uqualid pattern? RIGHTARROW formula ;

variant : VARIANT OCURLY one_variant (COMMA one_variant)+ CCURLY ;

one_variant : term (WITH variant_rel)? ;

variant_rel : lqualid ;
*/

invariant : INVARIANT OCURLY formula CCURLY ;

assertion : (ASSERT | ASSUME | CHECK) OCURLY formula CCURLY | ABSURD ;
/* ----------------------------------------------------- */
// WhyML expressions
/*
expr
    : integer
    | real
    | lqualid
    | op expr
    | expr op expr
    | expr OBRACKET expr CBRACKET
    | expr OBRACKET expr CBRACKET LEFTARROW expr
    | expr OBRACKET expr op expr CBRACKET
    | expr expr+
    | FUN binder+ spec* RIGHTARROW spec* expr
    | LET REC rec_defn IN expr
    | LET fun_defn IN expr
    | IF expr THEN expr (ELSE expr)?
    | expr SEMICOLUMN expr
    | LOOP invariant* variant? expr END
    | WHILE expr DO invariant* variant? expr DONE
    | FOR lident EQUAL expr (TO | DOWNTO) expr DO invariant* expr DONE
    | assertion
    | RAISE uqualid
    | RAISE OPAR uqualid expr CPAR
    | TRY expr WITH (VBAR handler)+ END
    | ANY type spec*
    | ABSTRACT expr spec*
    | LET pattern EQUAL expr IN expr
    | MATCH expr (COMMA expr)* WITH VBAR? expr_case (VBAR expr_case)* END
    | OPAR expr (COMMA expr)+ CPAR
    | OCURLY expr_field+ CCURLY
    | expr DOT lqualid
    | expr DOT lqualid LEFTARROW expr
    | OCURLY expr WITH expr_field+ CCURLY
    | expr COLUMN type
    | GHOST expr
    | label expr
    | SQUOTE uident COLUMN expr
    | OPAR expr
    ;
*/

expr_case : pattern RIGHTARROW expr ;

expr_field : lqualid EQUAL expr SEMICOLUMN ;

handler : uqualid pattern? RIGHTARROW expr ;
/* ----------------------------------------------------- */
// WhyML modules
module : MODULE uident_nq label* mdecl* END ;

mdecl
    : decl
    | TYPE mtype_decl (WITH mtype_decl)*
    | TYPE lident_nq (SQUOTE lident_nq)* invariant+
    | LET GHOST? lident_nq label* pgm_defn
    | LET REC rec_defn
    | VAL GHOST? lident_nq label* pgm_decl
    | EXCEPTION lident_nq label* type?
    | NAMESPACE IMPORT? uident_nq mdecl* END
    ;

mtype_decl : lident_nq label* (SQUOTE lident_nq label*)* mtype_defn ;

mtype_defn : // Empty
    | EQUAL type
    | EQUAL VBAR? type_case (VBAR type_case)* invariant*
    | EQUAL OCURLY mrecord_field (SEMICOLUMN mrecord_field)* CCURLY invariant*
    ;

mrecord_field : GHOST? MUTABLE? lident_nq label* COLUMN type ;

pgm_defn : fun_body | EQUAL FUN binder+ spec* RIGHTARROW spec* expr ;

pgm_decl : param+ (COLUMN result)? spec* ;
// Wrappers
rec_defn : fun_defn ; // Wrap
fun_body : param+ (COLUMN result)? spec* EQUAL spec* expr ; // Wrap (adapt)
/* ----------------------------------------------------- */
// WhyML files
mlwfile : (theory | module)* ;
/* ----------------------------------------------------- */
/* -------------------- Lexer rules -------------------- */
/* ----------------------------------------------------- */
// Keywords
QUANTIFIER : 'forall' | 'exists' ;
// ----------
ABSTRACT : 'abstract' ;
ABSURD : 'absurd' ;
ALIAS : 'alias' ;
ANY : 'any' ;
AS : 'as' ;
ASSERT : 'assert' ;
ASSUME : 'assume' ;
AT : 'at' ;
AXIOM : 'axiom' ;
BEGIN : 'begin' ;
BY : 'by' ;
CHECK : 'check' ;
CLONE : 'clone' ;
COINDUCTIVE : 'coinductive' ;
CONSTANT : 'constant' ;
DIVERGES : 'diverges' ;
DO : 'do' ;
DONE : 'done' ;
DOWNTO : 'downto' ;
ELSE : 'else' ;
END : 'end' ;
ENSURES : 'ensures' ;
EXCEPTION : 'exception' ;
EXPORT : 'export' ;
FALSE : 'false' | 'False' ;
FLOAT_KW : 'float' ;
FOR : 'for' ;
FUN : 'fun' ;
FUNCTION : 'function' ;
GHOST : 'ghost' ;
GOAL : 'goal' ;
IF : 'if' ;
IMPORT : 'import' ;
IN : 'in' ;
INDUCTIVE : 'inductive' ;
INVARIANT : 'invariant' ;
LEMMA : 'lemma' ;
LET : 'let' ;
LOOP : 'loop' ;
MATCH : 'match' ;
MODULE : 'module' ;
MUTABLE : 'mutable' ;
NAMESPACE : 'namespace' ;
NOT : 'not' ;
OLD : 'old' ;
PREDICATE : 'predicate' ;
RAISE : 'raise' ;
RAISES : 'raises' ;
RANGE : 'range' ;
READS : 'reads' ;
REC : 'rec' ;
REQUIRES : 'requires' ;
RETURNS : 'returns' ;
SO : 'so' ;
THEN : 'then' ;
THEORY : 'theory' ;
TO : 'to' ;
TRUE : 'true' | 'True' ;
TRY : 'try' ;
TYPE : 'type' ;
USE : 'use' ;
VAL : 'val' ;
VARIANT : 'variant' ;
WHILE : 'while' ;
WITH : 'with' ;
WRITES : 'writes' ;
/* ----------------------------------------------------- */
// Literals
fragment ALPHA : [a-zA-Z];
fragment SUFFIX : ALPHA | DIGIT | '\'' | '_' ;

LIDENT : [a-z] SUFFIX* | '_' SUFFIX+ ;
UIDENT : [A-Z] SUFFIX* ;
QIDENT : '\'' [a-z] SUFFIX* ;

fragment DIGIT : [0-9] ;
fragment HEXDIGIT : DIGIT | [a-f] | [A-F] ;
fragment OCTDIGIT : [0-7] ;
fragment BINDIGIT : [0-1] ;

INTEGER : DIGIT ( DIGIT | '_' )*
    | ('0x' | '0X') HEXDIGIT ( HEXDIGIT | '_' )*
    | ('0o' | '0O') OCTDIGIT ( OCTDIGIT | '_' )*
    | ('0b' | '0B') BINDIGIT ( BINDIGIT | '_' )*
    ;

REAL : DIGIT+ EXPONENT
    | DIGIT+ '.' DIGIT* EXPONENT?
    | DIGIT* '.' DIGIT+ EXPONENT?
    | ('0x' | '0X') HEXREAL HEXPONENT
    ;

HEXREAL : HEXDIGIT+
    | HEXDIGIT+ '.' HEXDIGIT*
    // | HEXDIGIT* '.' HEXDIGIT+ // Unwrap: prevents some unwanted recogs
    ;

fragment EXPONENT : ('e' | 'E') ('-' | '+')? DIGIT+ ;
fragment HEXPONENT : ('p' | 'P') ('-' | '+')? DIGIT+ ;
/* ----------------------------------------------------- */
// Long literals
LOCATION : '[#' STRING DIGIT+ DIGIT+ DIGIT+ ']' ;
ATTRIBUTE : '[@' (~('\n'|'\r'))*? ']' ;

fragment ESCAPED_QUOTE : '\\"' ;
STRING : '"' ( ESCAPED_QUOTE | ~('\n'|'\r') )*? '"' ;
/* ----------------------------------------------------- */
// Symbols
LEFTARROW : '<-' ;
RIGHTARROW : '->' ;
VBAR : '|' ;
SQUOTE : '\'' ;
SEMICOLUMN : ';' ;
COLUMN : ':' ;
EXCLAM : '!' ;
DOLLAR : '$' ;
AMPER : '&' ;
QMARK : '?' ;
ATSYM : '@' ;
CAP : '^' ;
SHARP : '#' ;

PLUS : '+' ;
MINUS : '-' ;
STAR : '*' ;
SLASH : '/' ;
PERCENT : '%' ;

EQUAL : '=' ;
LOWER : '<' ;
GREATER : '>' ;
TILDA : '~' ;

DOT : '.' ;
COMMA : ',' ;

EQUIV : '<->' ;

LOG_AND : '/\\' ;
PRG_AND : '&&' ;
LOG_OR : '\\/' ;
PRG_OR : '||' ;

OPAR : '(' ;
CPAR : ')' ;
OBRACKET : '[' ;
CBRACKET : ']' ;
OCURLY : '{' ;
CCURLY : '}' ;

UNDERSCORE : '_' ;
/* ----------------------------------------------------- */
// Operators
fragment OPCHAR1 : EQUAL | LOWER | GREATER | TILDA ;
fragment OPCHAR2 : PLUS | MINUS ;
fragment OPCHAR3 : STAR | SLASH | PERCENT ;
fragment OPCHAR4 : EXCLAM | DOLLAR | AMPER | QMARK | ATSYM | CAP | DOT | COLUMN | VBAR | SHARP ;
fragment OPCHAR : OPCHAR1 | OPCHAR2 | OPCHAR3 | OPCHAR4 ;

MULTIOP : OPCHAR OPCHAR+ ;
/* ----------------------------------------------------- */
// WS
ML_COMMENT : '(*' .*? '*)' -> skip ;
WS : [ \t\r\n]+ -> skip ;
/* ----------------------------------------------------- */
