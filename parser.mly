
%{
  open Lambda;;
%}

%token LAMBDA
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token SUCC
%token PRED
%token ISZERO
%token LET
%token LETREC
%token IN
%token BOOL
%token NAT
%token STRING

%token LCURLY
%token RCURLY
%token LPAREN
%token RPAREN
%token DOT
%token EQ
%token COLON
%token ARROW
%token COMMA
%token EOF
%token CONCAT

%token <string> STRINGO
%token <int> INTV
%token <string> STRINGV

%start s
%type <Lambda.command> s

%%

s :
    STRINGV EQ term EOF
      { Bind ($1, $3) }
    | term EOF
      { Eval $1 }

term :
    appTerm
      { $1 }
  | IF term THEN term ELSE term
      { TmIf ($2, $4, $6) }
  | LAMBDA STRINGV COLON ty DOT term
      { TmAbs ($2, $4, $6) }
  | LET STRINGV EQ term IN term
      { TmLetIn ($2, $4, $6) }
  | LETREC STRINGV COLON ty EQ term IN term
      { TmLetIn ($2, TmFix (TmAbs ($2, $4, $6)), $8) }

appTerm :
    pathTerm
      { $1 }
  | SUCC pathTerm
      { TmSucc $2 }
  | PRED pathTerm
      { TmPred $2 }
  | ISZERO pathTerm
      { TmIsZero $2 }
  | atomicTerm CONCAT atomicTerm
      { TmConcat ($1, $3) } 
  | appTerm pathTerm
      { TmApp ($1, $2) }

pathTerm :
  pathTerm DOT STRINGV
    { TmProj ($1, $3) }
  | pathTerm DOT INTV 
    { TmProj ($1, string_of_int $3) }
  | atomicTerm
    { $1 }

atomicTerm :
    LPAREN term RPAREN
      { $2 }
  | TRUE
      { TmTrue }
  | FALSE
      { TmFalse }
  | STRINGO
      { TmString $1 }
  | STRINGV
      { TmVar $1 }
  | INTV
      { let rec f = function
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f $1 }
  | LCURLY tupleFields RCURLY
    { TmTuple $2}
  
tupleFields : 
  term 
    {[$1]}
    | term COMMA tupleFields
      {$1 :: $3}

ty :
    atomicTy
      { $1 }
  | atomicTy ARROW ty
      { TyArr ($1, $3) }

atomicTy :
    LPAREN ty RPAREN  
      { $2 } 
  | BOOL
      { TyBool }
  | NAT
      { TyNat }
  | STRING
      { TyString }
  
  
  /* (***
  | LCURLY tupleFields RCURLY
    { TyTuple $2} TyTuple esta sin definir en lambda
  ***) */

 /* recordFields : 
   {[]}
  | notEmptyRecordFields
    {$1}

notEmptyRecordFields : 
  notEmptyRecordFieldType
    {[$1]}
  | notEmptyRecordFieldType COMMA notEmptyRecordFieldType
    {$1 :: $3}

notEmptyRecordFieldType :
  | STRINGV EQ term
      { $3 } */