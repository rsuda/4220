(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)

exception model_error;

fun typeOf(itree(inode("Expr",_), [ LogOr ] ), m) = typeOf(LogOr, m)
    
    (*Logical or*)
    | typeOf( itree(inode("LogOr",_),
        [
            LogOr,
            itree(inode("||",_), []),
            LogAnd
        ]
        ), m) = let
                    val t1 = typeOf(LogOr, m)
                    val t2 = typeOf(LogAnd, m)
                in
                    if t1 = t2 andalso t1 = BOOL then BOOL
                    else ERROR
                end

    | typeOf(itree(inode("LogOr",_), [ LogAnd ] ), m) = typeOf(LogAnd, m)
    
    (*Logical and*)
    | typeOf( itree(inode("LogAnd",_),
        [
            LogAnd,
            itree(inode("&&",_), []),
            LogEq
        ]
        ), m) = let
                    val t1 = typeOf(LogAnd, m)
                    val t2 = typeOf(LogEq, m)
                in
                    if t1 = t2 andalso t1 = BOOL then BOOL
                    else ERROR
                end

    | typeOf(itree(inode("LogAnd",_), [ LogEq ] ), m) = typeOf(LogEq, m)
    
    (*Equality*)
    | typeOf( itree(inode("LogEq",_),
        [
            LogEq,
            itree(inode("==",_), []),
            RelOp
        ]
        ), m) = let
                    val t1 = typeOf(LogEq, m)
                    val t2 = typeOf(RelOp, m)
                in
                    if t1 = t2 andalso t1 <> ERROR then BOOL
                    else ERROR
                end
    
    | typeOf( itree(inode("LogEq",_),
        [
            LogEq,
            itree(inode("!=",_), []),
            RelOp
        ]
        ), m) = let
                    val t1 = typeOf(LogEq, m)
                    val t2 = typeOf(RelOp, m)
                in
                    if t1 = t2 andalso t1 <> ERROR then BOOL
                    else ERROR
                end

    | typeOf(itree(inode("LogEq",_), [ RelOp ] ), m) = typeOf(RelOp, m)
    
    (*Relation operators*)
    | typeOf( itree(inode("RelOp",_),
        [
            RelOp,
            itree(inode("<",_), []),
            AddOp
        ]
        ), m) = let
                    val t1 = typeOf(RelOp, m)
                    val t2 = typeOf(AddOp, m)
                in
                    if t1 = t2 andalso t1 = INT then BOOL
                    else ERROR
                end
    
    | typeOf( itree(inode("RelOp",_),
        [
            RelOp,
            itree(inode("<=",_), []),
            AddOp
        ]
        ), m) = let
                    val t1 = typeOf(RelOp, m)
                    val t2 = typeOf(AddOp, m)
                in
                    if t1 = t2 andalso t1 = INT then BOOL
                    else ERROR
                end
                
    | typeOf( itree(inode("RelOp",_),
        [
            RelOp,
            itree(inode(">",_), []),
            AddOp
        ]
        ), m) = let
                    val t1 = typeOf(RelOp, m)
                    val t2 = typeOf(AddOp, m)
                in
                    if t1 = t2 andalso t1 = INT then BOOL
                    else ERROR
                end
    
    | typeOf( itree(inode("RelOp",_),
        [
            RelOp,
            itree(inode(">=",_), []),
            AddOp
        ]
        ), m) = let
                    val t1 = typeOf(RelOp, m)
                    val t2 = typeOf(AddOp, m)
                in
                    if t1 = t2 andalso t1 = INT then BOOL
                    else ERROR
                end

    | typeOf(itree(inode("RelOp",_), [ AddOp ] ), m) = typeOf(AddOp, m)
    
    (*Add and subtract operators*)
    | typeOf( itree(inode("AddOp",_),
        [
            AddOp,
            itree(inode("+",_), []),
            MulOp
        ]
        ), m) = let
                    val t1 = typeOf(AddOp, m)
                    val t2 = typeOf(MulOp, m)
                in
                    if t1 = t2 andalso t1 = INT then INT
                    else ERROR
                end
    
    | typeOf( itree(inode("AddOp",_),
        [
            AddOp,
            itree(inode("-",_), []),
            MulOp
        ]
        ), m) = let
                    val t1 = typeOf(AddOp, m)
                    val t2 = typeOf(MulOp, m)
                in
                    if t1 = t2 andalso t1 = INT then INT
                    else ERROR
                end
                
    | typeOf(itree(inode("AddOp",_), [ MulOp ] ), m) = typeOf(MulOp, m)
    
    (*Multiply, divide, and module operators*)
    | typeOf( itree(inode("MulOp",_),
        [
            MulOp,
            itree(inode("*",_), []),
            UnaryOp
        ]
        ), m) = let
                    val t1 = typeOf(MulOp, m)
                    val t2 = typeOf(UnaryOp, m)
                in
                    if t1 = t2 andalso t1 = INT then INT
                    else ERROR
                end
                
    | typeOf( itree(inode("MulOp",_),
        [
            MulOp,
            itree(inode("/",_), []),
            UnaryOp
        ]
        ), m) = let
                    val t1 = typeOf(MulOp, m)
                    val t2 = typeOf(UnaryOp, m)
                in
                    if t1 = t2 andalso t1 = INT then INT
                    else ERROR
                end
                
    | typeOf( itree(inode("MulOp",_),
        [
            MulOp,
            itree(inode("%",_), []),
            UnaryOp
        ]
        ), m) = let
                    val t1 = typeOf(MulOp, m)
                    val t2 = typeOf(UnaryOp, m)
                in
                    if t1 = t2 andalso t1 = INT then INT
                    else ERROR
                end
                
    | typeOf(itree(inode("MulOp",_), [ UnaryOp ] ), m) = typeOf(UnaryOp, m)
    
    (*Unary operators*)
    | typeOf( itree(inode("UnaryOp",_),
        [
            itree(inode("-",_), []),
            UnaryOp
        ]
        ), m) = let
                    val t1 = typeOf(UnaryOp, m)
                in
                    if t1 = INT then INT
                    else ERROR
                end
             
    | typeOf( itree(inode("UnaryOp",_),
        [
            itree(inode("!",_), []),
            UnaryOp
        ]
        ), m) = let
                    val t1 = typeOf(UnaryOp, m)
                in
                    if t1 = BOOL then BOOL
                    else ERROR
                end
                
    | typeOf(itree(inode("UnaryOp",_), [ ExpOp ] ), m) = typeOf(ExpOp, m)
    
    (*Base operator*)
    | typeOf( itree(inode("ExpOp",_),
        [
            Base,
            itree(inode("^",_), []),
            ExpOp
        ]
        ), m) = let
                    val t1 = typeOf(Base, m)
                    val t2 = typeOf(ExpOp, m)
                in
                    if t1 = t2 andalso t1 = INT then INT
                    else ERROR
                end
                
    | typeOf(itree(inode("ExpOp",_), [ Base ] ), m) = typeOf(Base, m)
    
    (*Expressions*)
    (*| typeOf( itree(inode("Expr",_),
        [
            Expr
        ]
        ), m) = typeOf(Expr, m)*)

    | typeOf( itree(inode("Base",_),
        [
            Expr
        ]
        ), m) = typeOf(Expr, m)
    
    | typeOf( itree(inode("Base",_),
        [
            itree(inode("|",_), [] ),
            Expr,
            itree(inode("|",_), [] )
        ]
        ), m) = let
                    val t = typeOf(Expr, m)
                in
                    if t = INT then INT
                    else ERROR
                end
        
    | typeOf( itree(inode("Base",_),
        [
            itree(inode("(",_), [] ),
            Expr,
            itree(inode(")",_), [] )
        ]
        ), m) = typeOf(Expr, m)
       
    (*Identifier*)
    | typeOf(itree(inode("identifier",_),
        [
            id_node
        ]
        ), m) = getType(accessEnv(getLeaf(id_node),m))
    
    (*Value*)
    | typeOf(itree(inode("Value",_),
        [
            itree(inode("true",_), [])
        ]
        ), m) = BOOL
    
    | typeOf(itree(inode("Value",_),
        [
            itree(inode("false",_), [])
        ]
        ), m) = BOOL
        
    | typeOf(itree(inode("Value",_),
        [
            integer
        ]
        ), m) = INT
    
    (*Pre Increment/decrement*)
    | typeOf( itree(inode("Incr",_),
        [
            id_node,
            itree(inode("++",_), [])
        ]
        ), m) = let
                    val t1 = getType(accessEnv(getLeaf(id_node), m))
                in
                    if t1 = INT then INT
                    else ERROR
                end
                
    | typeOf( itree(inode("Incr",_),
        [
            id_node,
            itree(inode("--",_), [])
        ]
        ), m) = let
                    val t1 = getType(accessEnv(getLeaf(id_node), m))
                in
                    if t1 = INT then INT
                    else ERROR
                end
    
    | typeOf( itree(inode("Incr",_),
        [
            itree(inode("++",_), []),
            id_node
        ]
        ), m) = let
                    val t1 = getType(accessEnv(getLeaf(id_node), m))
                in
                    if t1 = INT then INT
                    else ERROR
                end
                
    | typeOf( itree(inode("Incr",_),
        [
            itree(inode("--",_), []),
            id_node
        ]
        ), m) = let
                    val t1 = getType(accessEnv(getLeaf(id_node), m))
                in
                    if t1 = INT then INT
                    else ERROR
                end 
    | typeOf( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")
    | typeOf _ = raise Fail("Error in typeOf - this should never occur");

fun typeCheck( itree(inode("StmtList",_), [ Stmtlist ] ), m) = m
    
    (*Statement List*)
    | typeCheck ( itree(inode("StmtList",_),
                [
                    Stmt,
                    StmtList
                ]
                ), m0) = let
                            val m1 = typeCheck(Stmt, m0)
                            val m2 = typeCheck(StmtList, m1)
                         in
                            m2
                         end
    (*Might need one for epsilon*)
    (*
    | typeCheck ( itree(inode("StmtList",_),
                [
                    Stmt,
                    StmtList
                ]
                ), m0) = let
                            val m1 = typeCheck(stmt, m0)
                            val m2 = typeCheck(stmt_list, m1)
                         in
                            m2
                         end
    *)
    
    (*Stmt*)
    | typeCheck ( itree(inode("Stmt",_),
                [
                    Stmt,
                    itree(inode(";",_), [])
                ]
                ), m) = typeCheck(Stmt, m) 
    
    | typeCheck ( itree(inode("Stmt",_),
                [
                    Stmt
                ]
                ), m) = typeCheck(Stmt, m)
    
    (*Declaration*)
    | typeCheck ( itree(inode("Dec",_),
                [
                    itree(inode("int",_), []),
                    id_node
                ]
                ), m) = let
                            val id = getLeaf(id_node)
                            val (_,n,_) = m
                         in
                            updateEnv(id, INT, m)
                         end
                    
    | typeCheck ( itree(inode("Dec",_),
                [
                    itree(inode("bool",_), []),
                    id_node
                ]
                ), m) = let
                            val id = getLeaf(id_node)
                            val (_,n,_) = m
                         in
                            updateEnv(id, BOOL, m)
                         end
    
    (*Assignment*)               
    | typeCheck ( itree(inode("Assign",_),
                [
                    id_node,
                    itree(inode("=",_), []),
                    Expr
                ]
                ), m0) = let
                            val id = getLeaf(id_node)
                            val t1 = typeOf(Expr, m0)
                            val t2 = getType(accessEnv(id, m0))
                         in
                            if t1 = t2 andalso t1 <> ERROR then m0
                            else raise model_error
                         end
    
    (*Block*)
    | typeCheck ( itree(inode("Block",_),
                [
                    itree(inode("{",_), []),
                    StmtList,
                    itree(inode("}",_), [])
                ]
                ), m0) = let
                            val m1 = typeCheck(StmtList, m0)
                        in 
                            m0
                        end
    
    (*Conditional*)
    | typeCheck ( itree(inode("Cond",_),
                [
                    itree(inode("if",_), []),
                    itree(inode("(",_), []),
                    Expr,
                    itree(inode(")",_), []),
                    Block1,
                    itree(inode("else",_), []),
                    Block2
                ]
                ), m0) = let
                            val t = typeOf (Expr, m0)
                            val m1 = typeCheck (Block1, m0)
                            val m2 = typeCheck (Block2, m0)
                        in 
                            if t = BOOL then m0 
                            else raise model_error
                        end
                        
    | typeCheck ( itree(inode("Cond",_),
                [
                    itree(inode("if",_), []),
                    itree(inode("(",_), []),
                    Expr,
                    itree(inode(")",_), []),
                    Block
                ]
                ), m0) = let
                            val t = typeOf (Expr, m0)
                            val m1 = typeCheck (Block, m0)
                        in 
                            if t = BOOL then m0 
                            else raise model_error
                        end
                        
    (*Iter*)
    | typeCheck(itree(inode("Iter",_),
                    [
                        Iter
                    ]
            ),
          m
        ) = typeCheck(Iter, m)
    
    (*ForIter*)
    | typeCheck ( itree(inode("ForIter",_),
                [
                    itree(inode("for",_), []),
                    itree(inode("(",_), []),
                    assign1,
                    itree(inode(";",_), []),
                    expr,
                    itree(inode(";",_), []),
                    assign2,
                    itree(inode(")",_), []),
                    block
                ]
                ), m0) = let
                            val m1 = typeCheck( assign1, m0)
                            val t1 = typeOf (expr, m1)
                            val m2 = typeCheck( block, m1)
                            val m3 = typeCheck(assign2, m2)
                        in 
                            if t1 = BOOL then m0 
                            else raise model_error
                        end
                        
    (*WhileIter*)
    | typeCheck ( itree(inode("WhileIter",_),
                [
                    itree(inode("while",_), []),
                    itree(inode("(",_), []),
                    Expr,
                    itree(inode(")",_), []),
                    Block
                ]
                ), m0) = let
                            val t = typeOf (Expr, m0)
                            val m1 = typeCheck (Block, m0)
                        in 
                            if t = BOOL then m0 
                            else raise model_error
                        end
    
    (*Print*)
    | typeCheck ( itree(inode("Print",_),
                [
                    itree(inode("print",_), []),
                    itree(inode("(",_), []),
                    Expr,
                    itree(inode(")",_), [])
                ]
                ), m0) = let
                            val t = typeOf (Expr, m0)
                        in 
                            if t = ERROR then raise model_error 
                            else m0
                        end
    
  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








