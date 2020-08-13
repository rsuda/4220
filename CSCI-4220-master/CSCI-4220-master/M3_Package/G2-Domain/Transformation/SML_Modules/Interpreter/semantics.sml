(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)
fun power(x, 0) = 1
    | power(x, n) = x * power(x, n-1);

(*Expressions*)
fun E( itree(inode("Expr",_),
                [
                    LogOr
                ]
            ),
        m
    ) = E(LogOr, m)
    
 (*Logical or*)
| E ( itree(inode("LogOr",_),
                [
                    LogOr,
                    itree(inode("||",_), []),
                    LogAnd
                ]
            ),
        m0
    ) = let
            val (v1, m1) = E(LogOr, m0)
        in
            if toBool(v1) then (Boolean true, m1)
            else
                let
                    val (v2,m2) = E(LogAnd, m1)
                in
                    (Boolean(toBool(v1) orelse toBool(v2)), m2)
                end
            end
            
| E( itree(inode("LogOr",_),
                [
                    LogAnd
                ]
            ),
        m
    ) = E(LogAnd, m)
    
 (*Logical and*)
| E ( itree(inode("LogAnd",_),
                [
                    LogAnd,
                    itree(inode("&&",_), []),
                    LogEq
                ]
            ),
        m0
    ) = let
            val (v1, m1) = E(LogAnd, m0)
        in
            if toBool(v1) then
                let
                    val (v2,m2) = E(LogEq, m1)
                in
                    (Boolean(toBool(v1) andalso toBool(v2)), m2)
                end
            else (Boolean false, m1)
        end
            
| E( itree(inode("LogAnd",_),
                [
                    LogEq
                ]
            ),
        m
    ) = E(LogEq, m)
    
(*Logical equality*)
| E ( itree(inode("LogEq",_),
                [
                    LogEq,
                    itree(inode("==",_), []),
                    RelOp
                ]
            ),
        m0
    ) = let
            val (v1, m1) = E(LogEq, m0)
            val (v2, m2) = E(RelOp, m1)
        in
            (Boolean(v1 = v2), m2)
        end

| E ( itree(inode("LogEq",_),
                [
                    LogEq,
                    itree(inode("!=",_), []),
                    RelOp
                ]
            ),
        m0
    ) = let
            val (v1, m1) = E(LogEq, m0)
            val (v2, m2) = E(RelOp, m1)
        in
            (Boolean(v1 <> v2), m2)
        end

| E( itree(inode("LogEq",_),
                [
                    RelOp
                ]
            ),
        m
    ) = E(RelOp, m)

(*Relational operations*)
| E( itree(inode("RelOp",_),
                [
                    RelOp,
                    itree(inode("<",_), [] ),
                    AddOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(RelOp, m0)
          val (v2,m2) = E(AddOp, m1)
        in
          (Boolean(toInt(v1) < toInt(v2)), m2)
        end

| E( itree(inode("RelOp",_),
                [
                    RelOp,
                    itree(inode("<=",_), [] ),
                    AddOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(RelOp, m0)
          val (v2,m2) = E(AddOp, m1)
        in
          (Boolean(toInt(v1) <= toInt(v2)), m2)
        end

| E( itree(inode("RelOp",_),
                [
                    RelOp,
                    itree(inode(">",_), [] ),
                    AddOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(RelOp, m0)
          val (v2,m2) = E(AddOp, m1)
        in
          (Boolean(toInt(v1) > toInt(v2)), m2)
        end

| E( itree(inode("RelOp",_),
                [
                    RelOp,
                    itree(inode(">=",_), [] ),
                    AddOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(RelOp, m0)
          val (v2,m2) = E(AddOp, m1)
        in
          (Boolean(toInt(v1) > toInt(v2)), m2)
        end

| E( itree(inode("RelOp",_),
                [
                    AddOp
                ]
            ),
        m
    ) = E(AddOp, m)

(*Additive*)
 | E( itree(inode("AddOp",_),
                [
                    AddOp,
                    itree(inode("+",_), [] ),
                    MulOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(AddOp, m0)
          val (v2,m2) = E(MulOp, m1)
        in
          (Integer(toInt(v1) + toInt(v2)), m2)
        end
 
| E( itree(inode("AddOp",_),
                [
                    AddOp,
                    itree(inode("-",_), [] ),
                    MulOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(AddOp, m0)
          val (v2,m2) = E(MulOp, m1)
        in
          (Integer(toInt(v1) + toInt(v2)), m2)
        end

| E( itree(inode("AddOp",_),
                [
                    MulOp
                ]
            ),
        m
    ) = E(MulOp, m)

(*Multiplicitive*)
| E( itree(inode("MulOp",_),
                [
                    MulOp,
                    itree(inode("*",_), [] ),
                    UnaryOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(MulOp, m0)
          val (v2,m2) = E(UnaryOp, m1)
        in
          (Integer(toInt(v1) * toInt(v2)), m2)
        end

| E( itree(inode("MulOp",_),
                [
                    MulOp,
                    itree(inode("/",_), [] ),
                    UnaryOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(MulOp, m0)
          val (v2,m2) = E(UnaryOp, m1)
        in
          (Integer(toInt(v1) div toInt(v2)), m2)
        end
        
| E( itree(inode("MulOp",_),
                [
                    MulOp,
                    itree(inode("%",_), [] ),
                    UnaryOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(MulOp, m0)
          val (v2,m2) = E(UnaryOp, m1)
        in
          (Integer(toInt(v1) * toInt(v2)), m2)
        end

| E( itree(inode("MulOp",_),
                [
                    UnaryOp
                ]
            ),
        m
    ) = E(UnaryOp, m)

(*UnaryOp*)
| E( itree(inode("UnaryOp",_),
                [
                    itree(inode("-",_), [] ),
                    UnaryOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(UnaryOp, m0)
        in
          (Integer(~(toInt(v1))), m1)
        end

| E( itree(inode("UnaryOp",_),
                [
                    itree(inode("!",_), [] ),
                    UnaryOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(UnaryOp, m0)
        in
          (Boolean(not(toBool(v1))), m1)
        end
        
| E( itree(inode("UnaryOp",_),
                [
                    ExpOp
                ]
            ),
        m
    ) = E(ExpOp, m)
    
(*Exponent*)
| E( itree(inode("ExpOp",_),
                [
                    Base,
                    itree(inode("^",_), [] ),
                    ExpOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(ExpOp, m0)
          val (v2,m2) = E(Base, m1)
        in
          (Integer(power(toInt(v1),toInt(v2))), m2)
        end

| E( itree(inode("ExpOp",_),
                [
                    Base
                ]
            ),
        m
    ) = E(Base, m)

(*Expressions*)
| E( itree(inode("Base",_),
                [
                    itree(inode("(",_), [] ),
                    Expr,
                    itree(inode(")",_), [] )
                ]
            ),
        m
    ) = E(Expr, m)
    
| E( itree(inode("Base",_),
                [
                    itree(inode("|",_), [] ),
                    Expr,
                    itree(inode("|",_), [] )
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(Expr, m0)
        in
          (Integer(Int.abs(toInt(v1))), m1)
        end
 
| E( itree(inode("Base",_),
                [
                    identifier
                ]
            ),
        m
    ) = E(identifier, m)
    
(*Identifier*)
| E(itree(inode("identifier",_),
                [
                    id_node
                ]
            ),
        m
    ) = let
          val id = getLeaf(id_node)
          val loc = getLoc(accessEnv(id, m))
          val v = accessStore(loc, m)
        in
          (v, m)
        end

(*Value*)
 | E( itree(inode("Value",_),
                [
                    itree(inode("true",_), [] )
                ]
            ),
        m
    ) = (Boolean true, m)
    
  | E( itree(inode("Value",_),
                [
                    itree(inode("false",_), [] )
                ]
            ),
        m
    ) = (Boolean false, m)
  
  | E( itree(inode("Value",_),
                [
                    integer
                ]
            ),
        m
    ) = let
          val v = getLeaf(integer)
          val v_int = valOf(Int.fromString(v))
        in
          (Integer v_int, m)
        end

(*Increment and decrement*)
| E( itree(inode("Incr",_), 
                [ 
                    itree(inode("++",_), [] ),
                    id_node
                ] 
             ), 
        m0
    ) = let
          val id = getLeaf(id_node)
          val loc = getLoc(accessEnv(id, m0))
          val v = accessStore(loc, m0)
          val inc = Integer(toInt(v) + 1)
          val m1 = updateStore(loc, inc, m0)
        in
          (inc, m1)
        end

| E( itree(inode("Incr",_), 
                [ 
                    itree(inode("--",_), [] ),
                    id_node
                ] 
             ), 
        m0
    ) = let
          val id = getLeaf(id_node)
          val loc = getLoc(accessEnv(id, m0))
          val v = accessStore(loc, m0)
          val dec = Integer(toInt(v) - 1)
          val m1 = updateStore(loc, dec, m0)
        in
          (dec, m1)
        end

| E( itree(inode("Incr",_), 
                [ 
                    id_node,
                    itree(inode("++",_), [] )
                ] 
             ), 
        m0
    ) = let
          val id = getLeaf(id_node)
          val loc = getLoc(accessEnv(id, m0))
          val v = accessStore(loc, m0)
          val inc = Integer(toInt(v) + 1)
          val m1 = updateStore(loc, inc, m0)
        in
          (inc, m1)
        end

| E( itree(inode("Incr",_), 
                [ 
                    id_node,
                    itree(inode("--",_), [] )
                ] 
             ), 
        m0
    ) = let
          val id = getLeaf(id_node)
          val loc = getLoc(accessEnv(id, m0))
          val v = accessStore(loc, m0)
          val inc = Integer(toInt(v) - 1)
          val m1 = updateStore(loc, inc, m0)
        in
          (inc, m1)
        end

| E(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E root = " ^ x_root ^ "\n\n")
  
| E _ = raise Fail("error in Semantics.E - this should never occur")

(*Model*)
  (*Statement list*)
 fun M( itree(inode("StmtList",_),
                [ 
                    Stmt,
                    StmtList
                ] 
             ), 
        m0
    ) = let
          val m1 = M(Stmt, m0)
          val m2 = M(StmtList, m1)
        in
          m2
        end
 | M( itree(inode("StmtList", _), NIL), m0) = m0
        
 (*Statement*)
 | M( itree(inode("Stmt", _),
                [
                    Stmt,
                    itree(inode(";", _), [])
                ]
            ),
        m
    ) = M(Stmt, m)
 | M( itree(inode("Stmt", _),
            [
                Stmt
            ]
        ),
        m
    ) = M(Stmt, m)
    
  (*Declarations*)
  | M( itree(inode("Dec",_),
                [
                    itree(inode("int",_), [] ),
                    id_node
                ]
            ),
        (env, n, s)
    ) = let
          val id = getLeaf(id_node)
        in
            updateEnv(id, INT, (env, n, s))
        end
        
    | M( itree(inode("Dec",_),
                [
                    itree(inode("bool",_), [] ),
                    id_node
                ]
            ),
        (env, n, s)
    ) = let
          val id = getLeaf(id_node)
        in
            updateEnv(id, BOOL, (env, n, s))
        end
  
  (*Assignment*)
  | M( itree(inode("Assign",_),
                [
                    id_node,
                    itree(inode("=",_), [] ),
                    Expr
                ]
            ),
        m0
    ) = let
          val id = getLeaf(id_node)
          val (v, m1) = E(Expr, m0)
          val loc = getLoc(accessEnv(id, m1))
          val m2 = updateStore(loc, v, m1)
        in
          m2
        end
    
    (*Print*)
    | M( itree(inode("Print", _),
                [
                    itree(inode("print",_), []),
                    itree(inode("(",_), [] ),
                    Expr,
                    itree(inode(")",_), [] )
                ]
            ),
            m0
     ) = let
            val (v, m1) = E(Expr, m0)
            val str = varToString(v)
         in
            (print(str ^ "\n"); m1)
         end
    
    (*Conditional*)
    | M( itree(inode("Cond", _),
                [
                    itree(inode("if",_), []),
                    itree(inode("(",_), []),
                    Expr,
                    itree(inode(")",_), []),
                    Block1,
                    itree(inode("else",_), []),
                    Block2
                ]
             ),
            m0
      ) = let
               val (v, m1) = E(Expr, m0)
           in
                if toBool(v) then M(Block1, m1)
                else M(Block2, m1)
           end
           
    | M( itree(inode("Cond", _),
                [
                    itree(inode("if",_), []),
                    itree(inode("(",_), []),
                    Expr,
                    itree(inode(")",_), []),
                    Block
                ]
             ),
            m0
      ) = let
               val (v, m1) = E(Expr, m0)
           in
                if toBool(v) then M(Block, m1)
                else m1
           end
    
    (*Block*)
    | M( itree(inode("Block", _),
                [
                    itree(inode("{",_), []),
                    StmtList,
                    itree(inode("}",_), [])
                ]
            ),
           (env0, n0, s0)
      ) = let
            val (_, n1, s1) = M(StmtList, (env0, n0, s0))
            val m = (env0, n1, s1)
          in
            m
          end
    
    (*Iter*)
    | M( itree(inode("Iter",_),
                [
                    Iter
                ]
            ),
        m
    ) = M(Iter, m)
    
    (*ForIter*)
    | M( itree(inode("ForIter",_),
                [
                    itree(inode("for",_), []),
                    itree(inode("(",_), []),
                    assign1,
                    itree(inode(";",_),[]),
                    expr,
                    itree(inode(";",_),[]),
                    assign2,
                    itree(inode(")",_), []),
                    block
                ]
            ),
        m0
    ) = let
          val m1 = M(assign1, m0)
          
          fun aux(m2) = 
            let
                val (v, m3) = E(expr, m2)
            in
                if toBool(v) then
                    let
                        val m4 = M(block, m3)
                        val m5 = M(assign2, m4)
                        val m6 = aux(m5)
                    in
                        m6
                    end
                else m3
            end
            
        in
          aux(m1)
        end
    
    (*WhileIter*)
    | M( itree(inode("WhileIter",_),
                [
                    itree(inode("while",_), []),
                    itree(inode("(",_), []),
                    Expr,
                    itree(inode(")",_), []),
                    Block
                ]
            ),
        m0
    ) = let
          
          fun aux(m1) = 
            let
                val (v, m2) = E(Expr, m1)
            in
                if toBool(v) then
                    let
                        val m3 = M(Block, m2)
                        val m4 = aux(m3)
                    in
                        m4
                    end
                else m2
            end
        in
          aux(m0)
        end
    
  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








