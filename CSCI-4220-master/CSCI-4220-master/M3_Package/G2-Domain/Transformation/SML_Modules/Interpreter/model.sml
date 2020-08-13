exception runtime_error;

(* =========================================================================================================== *)
structure Model =

struct 

    (* =========================================================================================================== *)
    (* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
    *)
    fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 

    fun error msg = ( print msg; raise runtime_error );


    (* For your typeChecker you may want to have a datatype that defines the types 
    (i.e., integer, boolean and error) in your language. *)
    datatype types = INT | BOOL | ERROR;


    (* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
    *)
    datatype denotable_value =  Boolean of bool 
    | Integer of int;


    type loc   = int
    type env   = (string * types * loc) list
    type store = (loc * denotable_value) list

    (* ACCESS ENV *)
    fun accessEnv ( id1, (env, c, s) ) = 
    let 
        val msg = "Error: accessEnv " ^ id1 ^ " not found.";

        fun aux [] = error msg
        | aux ((id, t, loc)::env) = if id1 = id then (t, loc)
        else aux env
    in
        aux env
    end; 
    
    (* UPDATE ENV *)
    fun updateEnv (id, INT, (env, c, s)) = ((id, INT, c)::env, c + 1, s)
    | updateEnv (id, BOOL, (env, c, s)) = ((id, BOOL, c)::env, c + 1, s) 
    | updateEnv (id, ERROR, (env,c,s)) = ((id, ERROR, c)::env, c+1, s); 
    
    (* ACCESS STORE *)
    fun accessStore (loc, (env,c,s)) = 
    let 
        val msg = "ERROR: accessStore did not locate element at location " ^ Int.toString loc ^ ".\n"
        
        val found = List.find (fn (l,d) => l = loc) s
        fun aux item = if Option.isSome item then Option.valOf item else error msg
        val (l,d) = aux found
    in
        d
    end; 
    
    (* UPDATE STORE *)
    fun updateStore (loc, dv, (env, c, s)) = 
    let
        val found = List.find (fn (l,d) => l = loc) s
    in
        if found = NONE then (env, c, (loc,dv)::s)
        else (env, c, List.map (fn (l, d) => if l = loc then (l, dv) else (l,d)) s )
    end; 

    fun getLoc (t,loc) = loc;

    fun getType (t,loc) = t;

    (* From slides from Modeling Program State slides.*)
    fun typeToString BOOL = "bool"
    | typeToString INT = "int"
    | typeToString ERROR = "error";
    
    (* From slides from Modeling Program State slides.*)
    fun envEntryToString (id, t, loc) =
    "(" ^ id ^ "," ^ typeToString t ^ "," ^ Int.toString loc ^ ")";
    
    (* From slides from Modeling Program State slides.*)
    fun showEnv[] = print "\n"
    | showEnv (entry::env) = (
        print("\n" ^ envEntryToString entry);
        showEnv env
    );
    
    fun varToString (Boolean(x)) = Bool.toString x
    | varToString (Integer(x)) = Int.toString x;

    fun storeEntryToString (id, t, loc) =
    "(" ^ id ^ "," ^ typeToString t ^ "," ^ Int.toString loc ^ ")";
    
    fun showStore[] = print "\n"
    | showStore (entry::store) = (
        print("\n" ^ storeEntryToString entry);
        showStore store
    );

    fun showProgramState (env, n, s) = 
    (
        print("---ENVIRONMENT---");
        showEnv env;
        print("\n---COUNTER---\n");
        print(Int.toString n ^ "\n");
        print("---STORE---");
        showStore s
    );
    
    (* Helper Functions *)
    fun toInt(Boolean(x)) = error "invalid type for int"
    | toInt(Integer(x)) = x;

    fun toBool(Integer(x)) = error "invalid type for boolean"
    | toBool(Boolean(x)) = x;

    (* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
    incremented. *)
    val initialModel = ( []:env, 0:loc, []:store )

    (* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)

(*TESTS*)
(*
open Model;
accessEnv("x", ([],[]));
accessEnv("x", ([("x", INT, 0)], [])); 
showEnv [ ("x", BOOL, 0), ("y", INT, 27)];
accessStore(0, ([("x", INT, 0)], 1, [(0, Integer 8)]) );
accessStore(2, ([("x", BOOL, 0),("y", INT, 1),("z", BOOL, 2)], 3, [(0, Boolean true),(1, Integer 3),(2, Boolean false)]));
accessStore(0, ([("x", INT, 0)], 1, []));
*)
