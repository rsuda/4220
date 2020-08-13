# CSCI-4220 Project
Roy Thompson, Robin Suda, and Hilario Mendez-Vallejo

## Table of Contents
* Milestone 1
* Milestone 2

# Milestone 1
Roy Thompson, Robin Suda, and Hilario Mendez-Vallejo

## BNF Grammar

Below is the proposed BNF grammar for our language. Use `StmtList` as the start symbol. A program in our language is considered to be a list of Statements. 

```bnf
StmtList    ::= Stmt StmtList | ε
Stmt        ::= Skip ";" | Assign ";" | Dec ";" | Block | Iter | Cond | Print ";" | Expr ";"

Dec         ::= "int" identifier | "bool" identifier
Assign      ::= identifier "=" Expr
Incr		::= identifier "++" | identifier "--" | "++" identifier | "--" identifier

Block ::= "{" StmtList "}"

Cond 	::= "if" "(" Expr ")" Block "else" Block
		  | "if" "(" Expr ")" Block 

Iter        ::= ForIter | WhileIter
ForIter     ::= "for" "(" Expr ")" Block
WhileIter   ::= "while" "(" Expr ")" Block

Expr		::= LogOr
LogOr       ::= LogOr "||" LogAnd | LogAnd
LogAnd      ::= LogAnd "&&" LogEq | LogEq
LogEq       ::= LogEq "==" RelOp | LogEq "!=" RelOp | RelOp
RelOp       ::= RelOp "<" AddOp | RelOp "<=" AddOp | RelOp ">" AddOp | 
                RelOp ">=" AddOp | AddOp
AddOp       ::= AddOp "+" MulOp | AddOp "-" MulOp | MulOp
MulOp       ::= MulOp "*" UnaryOp | MulOp "/" UnaryOp | MulOp "%" UnaryOp | UnaryOp
UnaryOp		::= "-" UnaryOp | "!" UnaryOp | ExpOp 
ExpOp       ::= Base "^" ExpOp | Base
Base        ::= "|" Expr "|" | "(" Expr ")" | Value | identifier | Incr

Value		::= integer | boolean

Print       ::= "print" "(" Expr ")" ";"
```

## Regular Expressions

```
Reserved Symbols = {
	"-",
    "--",
	"!",
	"*",
	"/",
	"%",
	"+",
    "++",
	"<",
	"<=",
	"=",
	"==",
	">",
	">=",
	"||", 
	"else",
	"for",
	"if",
	"int",
	"print",
	"while",
    "^",
    "|"
}

identifier = [a-zA-Z]
integer = [1-9][0-9]* | 0
boolean = true | false
```

# Precedence and Associativity Table

The precedence and associativity table for the preceding language is described below. Note that the precedence is described in ascending order (0 => lowest)

|Operation|Precedence|Associativity|Nonterminal|
|---------|:--------:|:-----------:|----------:|
Expr | 0 (Low) | Left | `Expr`
Logical Or| 1 | Left| `LogOr`
Logical And| 2 | Left | `LogAnd`
Equality| 3 | Left | `LogEq`
Relational | 4 | Left | `RelOp`
Additive | 5 | Left | `AddOp`
Multiplicative | 6 | Left | `MulOp`
Unary Operator | 7 | Right | `UnaryOp`
Exponentiation | 8 | Right | `ExpOp` 
Absolute Value | 9 (High) | Left | `AbsOp`

# Milestone 2
Roy Thompson, Robin Suda, and Hilario Mendez-Vallejo

## Denotational Semantics

### Expressions
* We define a valuation function M such that `M: parse_expression * model -> model`
* We define a valuation function E' such that `E': parse_expression * model -> value * model`
* M is defined as a set of equations.
* E' is defined as a set of equations.
* We assume a Turing Complete context in which computation occurs. 

## Denotational Semantics

StmtList (List of Statements)
```sml
M([[stmt stmtList]], m0) =
    let
        val m1 = M(stmt1, m0)
        val m2 = M(stmtList1, m1)
    in
        m2
    end

| M([[ε]], m) = m
```

Stmt (Statement)
```sml
M([[skip ";"]], m0) = m0

| M([[assign ";"]], m0) =
    let
        val m1 = M(assign, m0)
    in
        m1
    end

| M([[dec ";"]], m0) =
    let
        val m1 = M(dec, m0)
    in
        m1
    end

| M([[block]], m0) =
    let
        val m1 = M(block, m0)
    in
        m1
    end

| M([[iter]], m0) =
    let
        val m1 = M(iter, m0)
    in
        m1
    end

| M([[cond]], m0) =
    let
        val m1 = M(cond, m0)
    in
        m1
    end

| M([[print]], m0) =
    let
        val m1 = M(print, m0)
    in
        m1
    end

| M([[expr ";"]], m0) =
    let
        val m1 = M(expr, m0)
    in
        m1
    end
```

Dec (Data Type)
```sml
M([["int" identifier]], m0) =
    let
        val m1 = updateEnv(identifier, int, new(), m0)
    in
        m1
    end

| M([["bool" identifier]], m0) =
    let
        val m1 = updateEnv(identifier, bool, new(), m0)
    in
        m1
    end
```

Assign (Assignment)
```sml
M([[identifier "=" expr1]], m0) =
    let
        val (v, m1) = E'(expr1, m0)
        val loc     = getLoc(accessEnv(identifier, m1))
        val m2      = updateStore(loc, v, m1)
    in
        m2
    end
```

Incr (Value/Variable)
```sml
E([[identifier "++"]], m) =
    let
        val v1 = E(identifier, m)
    in
        v1 + 1
    end
| E([[identifier "--"]], m) =
    let
        val v1 = E(identifier, m)
    in
        v1 - 1
    end
| E([["++" identifier]], m) =
    let
        val v1 = E(identifier, m)
    in
        1 + v1
    end
| E([["--" identifier]], m) =
    let
        val v1 = E(identifier, m)
    in
        1 - v1
    end
```

Block (Block)
```sml
M([["{" stmtList1 "}"]], m0) =
    let
        val m1 = (stmt1, m0)
    in
        m1
    end
```


Cond (Conditional)
```sml
M([["if" "("expr1")" block1 "else" block2]], m0) =
    let
        val (v, m1) = E’( expr1, m0 )
    in
	if v then M(block1, m1)
	else M(block2, m1)
    end

M([["if" "("expr1")" block]], m0) =
    let
        val (v, m1) = E’( expr1, m0 )
    in
	if v then M(block, m1)
	else m1
    end
```

Iter (Iterators)
```sml
M([[ForIter]], m0) =
    let
        val m1 = M(ForIter, m0)
    in
        m1
    end

| M([[WhileIter]], m0) =
    let
        val m1 = M(WhileIter, m0)
    in
        m1
    end
```

ForIter (For Loop)
```sml
M( [[ "for" "("expr1")" block ]], m ) = N (expr1, block1, m)
N(expr1, block1, m0 ) = 
	let
		val (v,m1) = E’( expr1, m0 )
	in
		if v then N ( expr1, block1, M(block1, m1) ) 
		else m1
	end
```

WhileIter (While Loop)
```sml
M( [[ "while" "("expr")" block ]], m0 ) =     
	let
		val (v,m1) = E’( expr, m0 )    
	in
		if v then 
			let              
				val m2 = M( block, m1 )    
				val m3 = M( [[ "while" "("expr")" block ]], m2 )           
			in    
				m3          
			end   
		else m1    
	end
```

Expr (Expression)
```sml
E'( [[ Expr1 ]], m ) = E'( expr1, m )
```

LogOr (Logical Or)
```sml
E'( [[ LogOr1 || LogAnd1 ]], m0 ) = 
    let 
        val (v1, m1) =  E'( LogOr1, m0 )
        val (v2, m2) = E'( LogAnd1, m1 )
    in 
        (v1 orelse v2, m2)
    end

| E'( [[ LogAnd1 ]] ) = E'( LogAnd1, m )
```

LogAnd (Logical And)
```sml
E'( [[ LogAnd1 "&&" LogEq1 ]], m0 ) = 
    let 
        val (v1, m1) = E'( LogAnd1, m0 )
        val (v2, m2) = E'( LogEq1, m1 )
    in
        ( v1 andalso v2, m2 )
    end

| E'( [[ LogEq1 ]], m ) = E'( LogEq1, m )
```

LogEq (Logical Equality)
```sml 
E'( [[ LogEq1 "==" RelOp1 ]], m0 ) = 
    let 
        val (v1, m1) = E'( LogEq, m0 )
        val (v2, m2) = E' ( LogEq, m1 )
    in
        ( v1 = v2, m2 )
    end
| E'( [[ LogEq "!=" RelOp1 ]], m0) = 
    let 
        val (v1, m1) = E'( LogEq, m0 )
        val (v2, m2) = E' ( LogEq, m1 )
    in
        ( v1 <> v2, m2 )
    end
| E' ( [[ RelOp1 ]], m ) = E' ( RelOp1, m )
```

RelOp1 (Relational Operators)
```sml
E' ( [[ RelOp1 < AddOp1 ]], m0 ) = 
    let
        val (v1, m1) = E'(RelOp1, m0)
        val (v2, m2) = E'(AddOp1, m1)
    in
        ( v1 < v2 , m2 )
    end
| E' ( [[ RelOp1 <= AddOp1 ]], m0 ) = 
    let
        val (v1, m1) = E'(RelOp1, m0)
        val (v2, m2) = E'(AddOp1, m1)
    in
        ( v1 <= v2 , m2 )
    end
| E' ( [[ RelOp1 > AddOp1 ]], m0 ) = 
    let
        val (v1, m1) = E'(RelOp1, m0)
        val (v2, m2) = E'(AddOp1, m1)
    in
        ( v1 > v2 , m2 )
    end
| E' ( [[ RelOp1 >= AddOp1 ]], m0 ) = 
    let
        val (v1, m1) = E'(RelOp1, m0)
        val (v2, m2) = E'(AddOp1, m1)
    in
        ( v1 >= v2 , m2 )
    end
| E' ( [[ AddOp1 ]], m ) = E'( AddOp1, m )
```

AddOp1 (Additive Operators)
```sml
E'( [[ AddOp1 "+" MulOp1 ]], m0 ) = 
    let 
        val (v1, m1) = E'(AddOp1, m0)
        val (v2, m2) = E'(MulOp1, m1)
    in
        (v1 + v2, m2)
    end
| E'( [[ AddOp1 "-" MulOp1 ]], m0 ) = 
    let 
        val (v1, m1) = E'(AddOp1, m0)
        val (v2, m2) = E'(MulOp1, m1)
    in
        (v1 - v2, m2)
    end
| E'( [[ MulOp1 ]], m ) = E'( MulOp1, m )
```

MulOp1 (Multiplicitive Operators)
```sml 
E'( [[ MulOp1 "*" UnaryOp1 ]], m0 ) = 
    let
        val (v1, m1) = E'(MulOp1, m0)
        val (v2, m2) = E'(UnaryOp1, m1)
    in
        (v1 * v2, m2)
    end
| E'( [[ MulOp1 "/" UnaryOp1 ]], m0 ) = 
    let
        val (v1, m1) = E'(MulOp1, m0)
        val (v2, m2) = E'(UnaryOp1, m1)
    in
        (v1 div v2, m2)
    end
| E'( [[ MulOp1 "%" UnaryOp1 ]], m0 ) = 
    let
        val (v1, m1) = E'(MulOp1, m0)
        val (v2, m2) = E'(UnaryOp1, m1)
    in
        (v1 mod v2, m2)
    end
| E'( [[ UnaryOp1 ]], m ) = E'( UnaryOp1, m )
```

UnaryOp (Unary Operator)
```sml
E'( [[ "-" UnaryOp1 ]], m0 ) = 
    let 
        val (v1, m1) = E'( UnaryOp1, m0 )
    in 
        (v1 - (2 * v1), m1)
    end
| E'( [[ "!" UnaryOp1 ]], m0 ) = 
    let
        val (v1, m1) = E'( UnaryOp1, m0 )
    in 
        ( not(v1), m1 )
    end    
| E'( [[ ExpOp1 ]], m ) = E'( ExpOp1, m)
```

ExpOp1 (Exponentiation)
```sml
fun power(x, 0) = 1 | power(x, n) = x * power(x,n-1);  

E'( [[ Base1 "^" ExpOp1 ]], m0 ) = 
    let 
        val (v1, m1) = E'(Base1, m0)
        val (v2, m2) = E'(ExpOp1, m1)
    in
        (power(v1, v2), m2)
    end
| E'( [[ Base1 ]], m ) = E'( Base1, m ) 
```

Base (Absolute Value, Parenthetical Expression, Value, and Identifier)
```sml
E'( [[ "|" Expr1 "|" ]], m0 ) = 
    let 
        val (v1, m1) = E'(Base1, m0)
    in
       ( v1 * ((v>0) - (v<0)) , m1)
    end
| E'( [[ "(" Expr1 ")" ]], m ) = E'( Expr1, m )
| E'( [[ identifier ]], m ) = 
    let
        val loc = getLoc(accessEnv(identifier, m))
        val v = accessStore(loc, m)
    in
        (v, m)
    end
| E'( [[ Value1 ]], m ) = E'(Value1, m)
| E'( [[ Incr1 ]], m ) = E'(Incr1, m)
```

Value (Integer and Boolean)
```sml
E’( [[ integer ]], m ) = ( integer, m )
| E’( [[ boolean ]], m ) = ( boolean, m )
```


Print (Print Values)
```sml
M([["print" "(" expr0 ")" ";"]], expr0) = print(expr0)
```