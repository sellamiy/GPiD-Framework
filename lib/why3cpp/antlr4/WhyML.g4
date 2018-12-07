/* ----------------------------------------------------- */
/* ----------------------- WhyML ----------------------- */
/* ----------------------------------------------------- */
grammar WhyML;
/* ----------------------------------------------------- */
/* ----------------------- Parser ---------------------- */
/* ----------------------------------------------------- */
// Lexical wrappers
infixop4 : W_INFIXOP4 SQUOTE* ;
infixop3 : (STAR | SLASH | PERCENT | W_INFIXOP3) SQUOTE* ;
infixop2 : (PLUS | MINUS | W_INFIXOP2) SQUOTE* ;
infixop1 : (EQUAL | LOWER | GREATER | TILDA | W_INFIXOP1) SQUOTE* ;
tightop : (EXCLAM | QMARK | W_TIGHTOP) SQUOTE* ;
prefixop : (infixop1 | infixop2 | infixop3 | infixop4) SQUOTE* ;

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
type : w_type_lit (RIGHTARROW type)? ;

w_type_lit
    : lqualid type_arg+
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
    : priority_term_constructs w_term_continuation?
    | AT term SQUOTE uident // 6.6.1 addition
    | OLD term
    ;

w_term_continuation
    : AT uident
    | (COMMA term)+
    ;

priority_term_constructs
    : MATCH term WITH term_case+ END
    | QUANTIFIER quant_vars triggers? DOT term
    | qualifier? BEGIN term END
    | priority_term_let
    ;

priority_term_let
    : IF term THEN term ELSE term
    | LET pattern EQUAL term IN term
    | LET symbol param+ EQUAL term IN term
    | FUN param+ RIGHTARROW term
    | priority_term_label
    ;

priority_term_label
    : attribute+ priority_term_cast
    | priority_term_cast
    ;

priority_term_cast
    : priority_term_equiv (COLUMN type)?
    ;

priority_term_equiv
    : priority_term_byso ((RIGHTARROW | EQUIV) priority_term_let)?
    ;

priority_term_byso
    : priority_term_or ((BY | SO) priority_term_let)?
    ;

priority_term_or
    : priority_term_and ((PRG_OR | LOG_OR) priority_term_let)?
    ;

priority_term_and
    : priority_term_not ((PRG_AND | LOG_AND) priority_term_let)?
    ;

priority_term_not
    : NOT priority_term_eq
    | priority_term_eq
    ;

priority_term_eq
    : priority_term_plus (infixop1 priority_term_let)?
    ;

priority_term_plus
    : priority_term_mult (infixop2 priority_term_let)?
    ;

priority_term_mult
    : priority_term_low (infixop3 priority_term_let)?
    ;

priority_term_low
    : priority_term_tight (infixop4 priority_term_let)?
    ;

priority_term_tight
    : prefixop priority_term_let
    | tightop priority_term_appl
    | priority_term_appl
    ;

priority_term_appl
    : priority_term_brackets term*
    ;

priority_term_brackets
    : priority_term_lit priority_term_brackets_continuation?
    ;

priority_term_brackets_continuation
    : DOT lqualid
    | OBRACKET term CBRACKET SQUOTE*
    | OBRACKET term LEFTARROW term CBRACKET SQUOTE*
    | OBRACKET term DOT DOT term CBRACKET SQUOTE*
    | OBRACKET term DOT DOT CBRACKET SQUOTE*
    | OBRACKET DOT DOT term CBRACKET SQUOTE*
    ;

priority_term_lit
    : integer
    | real
    | boolean
    | OPAR CPAR
    | qualid
    | OCURLY term_field+ CCURLY
    | OCURLY term WITH term_field+ CCURLY
    | priority_term_parentheses
    ;

priority_term_parentheses
    : qualifier? OPAR term CPAR
    ;

term_field : lqualid EQUAL term SEMICOLUMN ;

qualid : qualifier? (lident_ext | uident) ;

lident_ext : lident
    | OPAR ident_op CPAR
    | OPAR ident_op CPAR (VBAR | SQUOTE) uident // Warning : Not conform
    ;

ident_op
    : infixop1
    | infixop2
    | infixop3
    | infixop4
    | prefixop UNDERSCORE
    | tightop UNDERSCORE?
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

pattern : w_pattern_lit w_pattern_continuation? ;

w_pattern_lit
    : binder
    | OPAR CPAR
    | OCURLY (lqualid EQUAL pattern SEMICOLUMN)+ CCURLY
    | uqualid pattern*
    | GHOST pattern
    | qualifier? OPAR pattern CPAR
    ;

w_pattern_continuation
    : AS GHOST? bound_var
    | COMMA pattern
    | VBAR pattern
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
    : GHOST? priority_expr_constructs w_expr_continuation?
    | w_let_expressions
    ;

w_expr_continuation
    : (COMMA expr)+
    | spec+
    | SEMICOLUMN expr/*_Unsafe*/?
    ;

w_let_expressions
    : expr_r_letpattern
    | LET fun_defn IN expr
    | LET REC fun_defn (WITH fun_defn)* IN expr
    | FUN param+ spec* RIGHTARROW spec* expr
    ;

priority_expr_constructs
    : MATCH expr WITH (VBAR pattern RIGHTARROW expr)+ END
    | qualifier? BEGIN spec* expr END
    | LOOP invariant* variant? expr END
    | WHILE expr DO invariant* variant? expr DONE
    | expr_r_forloop
    | RAISE uqualid
    | RAISE OPAR uqualid expr CPAR
    | TRY expr WITH (VBAR handler)+ END
    | assertion
    | priority_expr_if
    ;

priority_expr_if
    : IF priority_expr_label THEN priority_expr_constructs (ELSE priority_expr_constructs)?
    | ANY result spec*
    | priority_expr_label
    ;

priority_expr_label
    : attribute+ priority_expr_cast
    | priority_expr_cast
    ;

priority_expr_cast
    : priority_expr_or (COLUMN priority_expr_if)?
    ;

priority_expr_or
    : priority_expr_and (PRG_OR priority_expr_if)?
    ;

priority_expr_and
    : priority_expr_not (PRG_AND priority_expr_if)?
    ;

priority_expr_not
    : NOT priority_expr_eq
    | priority_expr_eq
    ;

priority_expr_eq
    : priority_expr_plus priority_expr_eq_continuation?
    ;

priority_expr_eq_continuation
    : LEFTARROW priority_expr_if
    | infixop1 priority_expr_if
    ;

priority_expr_plus
    : priority_expr_mult (infixop2 priority_expr_if)?
    ;

priority_expr_mult
    : priority_expr_low (infixop3 priority_expr_if)?
    ;

priority_expr_low
    : priority_expr_tight (infixop4 priority_expr_if)?
    ;

priority_expr_tight
    : prefixop priority_expr_if
    | tightop priority_expr_appl
    | priority_expr_appl
    ;

priority_expr_appl
    : priority_expr_brackets priority_expr_tight*
    ;

priority_expr_brackets
    : priority_expr_lit priority_expr_brackets_continuation?
    ;

priority_expr_brackets_continuation
    : DOT lqualid
    | OBRACKET expr CBRACKET SQUOTE*
    | OBRACKET expr LEFTARROW expr CBRACKET SQUOTE*
    | OBRACKET expr DOT DOT expr CBRACKET SQUOTE*
    | OBRACKET expr DOT DOT CBRACKET SQUOTE*
    | OBRACKET DOT DOT expr CBRACKET SQUOTE*
    ;

priority_expr_lit
    : integer
    | real
    | boolean
    | OPAR CPAR
    | qualid
    | OCURLY (lqualid EQUAL expr SEMICOLUMN)+ CCURLY
    | OCURLY expr WITH (lqualid EQUAL expr SEMICOLUMN)+ CCURLY
    | expr_r_parentheses
    ;

fun_defn : fun_head spec* EQUAL spec* priority_expr_if ;

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

expr_r_parentheses : qualifier? OPAR priority_expr_if CPAR ;

expr_r_letpattern : LET pattern EQUAL priority_expr_if IN expr ;

expr_r_forloop : FOR lident EQUAL expr (TO | DOWNTO) expr DO invariant* expr DONE ;

// Wrap handlers

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
    | tightop term
    | prefixop term
    | term infixop4 term
    | term infixop3 term
    | term infixop2 term
    | term infixop1 term
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

fragment OPCHAR1234 : OPCHAR1 | OPCHAR2 | OPCHAR3 | OPCHAR4 ;
fragment OPCHAR234 : OPCHAR2 | OPCHAR3 | OPCHAR4 ;
fragment OPCHAR34 : OPCHAR3 | OPCHAR4 ;

W_TIGHTOP : (EXCLAM | QMARK) OPCHAR4* ;
// PREFIXOP : OPCHAR1234+ ;
W_INFIXOP4 : OPCHAR4+ ;
W_INFIXOP3 : OPCHAR34* OPCHAR3 OPCHAR34* ;
W_INFIXOP2 : OPCHAR234* OPCHAR2 OPCHAR234* ;
W_INFIXOP1 : OPCHAR1234* OPCHAR1 OPCHAR1234* ;
/* ----------------------------------------------------- */
// WS
ML_COMMENT : '(*' .*? '*)' -> skip ;
WS : [ \t\r\n]+ -> skip ;
/* ----------------------------------------------------- */
