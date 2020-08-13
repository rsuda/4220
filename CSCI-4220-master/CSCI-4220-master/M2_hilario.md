## Denotational Semantics

Below is a denotational description of the semantics of the language. 

```
StmtList    ::= Stmt StmtList | Stmt | ε
```
```sml
M([[stmt stmtList]], m0) =
    let
        val m1 = M(stmt1, m0)
        val m2 = M(stmtList1, m1)
    in
        m2
    end

| M([[stmt1]], m0) =
    let
        val m1 = M(stmt1, m0)
    in
        m1
    end

| M([[ε]], m) = m
```
```
Stmt        ::= Skip ";" | Assign ";" | Dec ";" | Block | Iter | Cond | Print ";" | Expr ";"
```
```sml
M([[skip ";"]], m) =
    let
        val m1 = M(skip, m)
    in
        m1
    end

| M([[assign ";"]], m) =
    let
        val m1 = M(assign, m)
    in
        m1
    end

| M([[dec ";"]], m) =
    let
        val m1 = M(dec, m0)
    in
        m1
    end

| M([[block]], m) =
    let
        val m1 = M(block, m)
    in
        m1
    end

| M([[iter]], m) =
    let
        val m1 = M(iter, m)
    in
        m1
    end

| M([[cond]], m) =
    let
        val m1 = M(cond, m)
    in
        m1
    end

| M([[print]], m) =
    let
        val m1 = M(print, m)
    in
        m1
    end

| M([[expr ";"]], m) =
    let
        val m1 = M(expr, m)
    in
        m1
    end
```
```
Dec         ::= "int" Id | "bool" Id
```
```sml
M([["int" id]], m0) =
    let
        val m1 = updateEnv(id, int, new(), m0)
    in
        m1
    end

| M([["bool" id]], m0) =
    let
        val m1 = updateEnv(id, bool, new(), m0)
    in
        m1
    end
```
```
Assign      ::= Id "=" Expr
```
```sml
M([[id "=" expr1]], m0) =
    let
        val (v, m1) = E'(expr1, m0)
        val loc     = getLoc(accessEnv(id, m1))
        val m2      = updateStore(loc, v, m1)
    in
        m2
    end
```
```
Id          ::= Id | Id "++" | Id "--" | "++" Id | "--" Id
```
```sml
M([[id]], m0) = m0
| E([[id "++"]], m) =
    let
        val v1 = E(id, m)
    in
        v1 + 1
    end
| E([[id "--"]], m) =
    let
        val v1 = E(id, m)
    in
        v1 - 1
    end
| E([["++" id]], m) =
    let
        val v1 = E(id, m)
    in
        1 + v1
    end
| E([["--" id]], m) =
    let
        val v1 = E(id, m)
    in
        1 - v1
    end
```
```
Block       ::= "{" StmtList "}"
```
```sml
M([["{" stmtList1 "}"]], m0) =
    let
        val m1 = (stmt1, m0)
    in
        m1
    end
```
```
Cond 	    ::= If | If Else
```
```sml
M([[if]], m0) =
    let
        val m1 = M(if, m0)
    in
        m1
    end

| M([[if else]], m0) =
    let
        val m1 = M(if else, m0)
    in
        m1
    end 
```
```
AbsOp       ::= "|" AbsOp "|" | Expr
```
```sml
M([["|" absOp1 "|"]], m0) =
    let
        val m1 = M(absOp1, m0)
    in
        m1
    end

| M([[expr]], m0) =
    let
        val m1 = M(expr, m0)
    in
        m1
    end
```
```
Print       ::= "print" "(" Expr ")" ";"
```
```sml
M([["print" "(" expr1 ")" ";"]], m0) =
    let
        val m1 = print(expr1)
    in
        m1
    end
```