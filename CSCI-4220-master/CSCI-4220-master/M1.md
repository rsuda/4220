# Milestone 1
Roy Thompson, Robin Suda, and Hilario Mendez-Vallejo

## BNF Grammar

Below is the proposed BNF grammar for our language. Use `StmtList` as the start symbol. A program in our language is considered to be a list of Statements. 

```bnf
StmtList    ::= Stmt StmtList | ε
Stmt        ::= Skip ";" | Assign ";" | Dec ";" | Block | Iter | Cond | Print ";" | Expr ";"

Dec         ::= "int" Id | "bool" Id
Assign      ::= Id "=" Expr
Incr		::= Id "++" | Id "--" | "++" Id | "--" Id

Block ::= "{" StmtList "}"

Cond 	::= "if" "(" Expr ")" Block "else" Block
		  | "if" "(" Expr ")" Block 

Iter        ::= ForIter | WhileIter
ForIter     ::= "for" "(" Assign ";" Expr ";" Expr ")" Block
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
Base        ::= "|" Expr "|" | "(" Expr ")" | Value | id | Incr

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
Exponentiation | 7 | Right | `ExpOp` 
Absolute Value | 8 (High) | Left | `AbsOp`

