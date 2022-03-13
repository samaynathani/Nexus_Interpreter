use "ast.sml";
use "exceptions.sml";
   
open HashTable;
val hash_fn : string->word = HashString.hashString;
val cmp_fn : string*string->bool = (op =);
val initial_size : int = 101;
val prev_classes: (string, string list) hash_table = mkTable (hash_fn, cmp_fn) (initial_size, UndeclaredVariableAssignmentException "Class undeclared");
val namespace : (string, class) hash_table = mkTable (hash_fn, cmp_fn) (initial_size, UndeclaredVariableAssignmentException "Class undeclared");


fun evaluate_ids (declarations : string list, statetable : (string, value) hash_table) : unit =
   case declarations of
      [] => ()
   |  x::xs =>
         case (find statetable x) of
            NONE => 
               (insert statetable (x, VALUE_NONE);
               evaluate_ids (xs, statetable);
               ())
         |  _ => raise VariableRedeclarationException x
;

fun evaluate_func_decls (func_decls : (string * function) list, statelist : ((string, value) hash_table) list ) : unit =
   case func_decls of
      [] => ()
   |  x::xs =>
         let
           val func_name = #1 x
           val func = #2 x
           val headtable = hd statelist
         in
           case (find headtable func_name) of
            NONE => 
               (insert headtable (func_name, CLOSURE (func,  statelist,  ref ()));
               evaluate_func_decls (xs, statelist);
               ())
         |  _ => raise VariableRedeclarationException func_name
         end
;


fun evaluate_identifier (id : string) (statetable :  (string, value) hash_table) : value =
   let
     val find_id = find statetable id
   in
     case find_id of 
         NONE => raise UndeclaredVariableException id
      |  SOME a => a
   end
;

fun print_value_to_string (v : value) : string =
   case v of 
      VALUE_NUMBER n => if n > ~1
                        then Int.toString n
                        else "-" ^ Int.toString (~n)
   |  VALUE_BOOL b => Bool.toString b
   |  VALUE_STRING s => s
   |  VALUE_NONE => "none"
   |  CLOSURE _ => "function"
   |  METHOD _ => "method"
   |  VALUE_OBJECT _ => "object"
;

fun map_value_to_string (v : value) : string =
   case v of 
      VALUE_NUMBER n => "number"
   |  VALUE_BOOL b => "boolean"
   |  VALUE_STRING s => "string"
   |  VALUE_NONE => "none"
   |  CLOSURE _ => "function"
   |  METHOD _ => "method"
   |  VALUE_OBJECT _ => "object"
;

fun search_states (states : ((string, value) hash_table) list, eid : string) : value = 
   case states of 
      [] => raise UndeclaredVariableException eid
   |  x::xs =>
         let
           val statetable = hd states
         in
           (case (find statetable eid) of
                     NONE => search_states (xs, eid)
                  |  SOME x => x)
         end        
;

fun search_states_assign (states : ((string, value) hash_table) list, eid : string, v : value) : value =
   case states of 
      [] => raise UndeclaredVariableAssignmentException eid
   |  x::xs =>
      let
        val statetable = hd states
      in
           (case (find statetable eid) of
               NONE => search_states_assign (xs, eid, v)
            |  SOME y => (evaluate_identifier eid statetable;
                           insert statetable (eid, v);
                           v))
      end
;

fun evaluate_obj_decls (decls : string list) (state : (string, value) hash_table) : unit = 
   case decls of 
      [] => ()
   |  x::xs =>
         case find state x of 
            NONE => (insert state (x, VALUE_NONE);
                     evaluate_obj_decls xs state;
                     ())
         |  _ => raise VariableRedeclarationException x
;

fun evaluate_super_obj_decls (decls : string list) (state : (string, value) hash_table) : unit = 
   case decls of 
      [] => ()
   |  x::xs =>
         if List.exists (fn (y : string) => y = x) xs
         then raise VariableRedeclarationException x
         else (case find state x of 
                  NONE => (
                     insert state (x, VALUE_NONE);
                     evaluate_super_obj_decls xs state
                     )
               |  SOME _ => evaluate_super_obj_decls xs state)
;

fun evaluate_obj_methods (func_decls : (string * function) list) (state : (string, value) hash_table) (myobj : value) : unit =
   let
     val newstate : (string, value) hash_table = mkTable (hash_fn, cmp_fn) (initial_size, UndeclaredVariableAssignmentException "Variable undeclared")
   in
     case func_decls of
      [] => ()
   |  (fname, fdef)::rest =>
         case find state fname of
            NONE => (
               insert newstate ("this", myobj);
               insert state (fname, CLOSURE(fdef, newstate :: [state], ref ()));
               evaluate_obj_methods rest state myobj;
               ()
               )
         |  _ => raise VariableRedeclarationException fname
   end
;

fun evaluate_super_obj_methods (func_decls : (string * function) list) (state : (string, value) hash_table) (myobj : value) : unit =
   let
     val newstate : (string, value) hash_table = mkTable (hash_fn, cmp_fn) (initial_size, UndeclaredVariableAssignmentException "Variable undeclared")
   in
     case func_decls of
      [] => ()
   |  (fname, fdef)::rest =>
         if List.exists (fn (y : (string * function)) => (#1 y) = fname) rest
         then raise VariableRedeclarationException fname
         else (
               case find state fname of 
                  NONE => (
                     insert newstate ("this", myobj);
                     insert state (fname, CLOSURE(fdef, newstate :: [state], ref ()));
                     evaluate_super_obj_methods rest state myobj
                     )
               |  SOME _ => evaluate_super_obj_methods rest state myobj
               )
   end
;

fun search_classes (classname : string) : class =
   case find namespace classname of 
      NONE => raise NewException classname
   |  SOME class => class
;

fun evaluate_new_exp (class : string) (statelist : ((string, value) hash_table) list) : value =
   let
     val myclass = search_classes class
     val obj_decls : (string, value) hash_table = mkTable (hash_fn, cmp_fn) (initial_size, UndeclaredVariableAssignmentException "Variable undeclared")
     val instance = VALUE_OBJECT(myclass, obj_decls :: statelist, ref ())
   in
      case myclass of {name, super, decls, funcs} =>
      (
         evaluate_obj_decls decls obj_decls;
         evaluate_obj_methods funcs obj_decls instance;
         
         (if isSome (#super myclass)
         then (
            case find namespace (valOf super) of
               NONE =>  raise UnknownSuperException (name, valOf super)
            |  SOME superclass => 
               (
                  evaluate_super_obj_decls (#decls superclass) obj_decls;
                  evaluate_super_obj_methods (#funcs superclass) obj_decls instance;
                  ()
               )
         )
         else ()
         );
         instance
      )
   end
;

fun evaluate_classes (classes : class list) (namespace : (string, class) hash_table) : unit =
   case classes of
      [] => ()
   |  x::xs =>
         case x of 
            {name, super, decls, funcs} => (
               (if isSome super
               then (
                  case find namespace (valOf super) of
                     NONE =>  raise UnknownSuperException (name, valOf super)
                  |  SOME _ => ())
               else ()
               );
               (case (find namespace name) of 
                  NONE => (
                     (case find prev_classes "old" of 
                        NONE => insert prev_classes ("old", [])
                     |  SOME v => ());
                  (insert prev_classes ("old", name::(lookup prev_classes "old")));
                  (insert namespace (name, x));
                  (evaluate_classes xs namespace);
                  ())
            |   _ => raise ClassRedeclarationException name))
;


fun evaluate_binary_op (bop : binaryOperator) (lftexp : expression) (rhtexp : expression) (states :  ((string, value) hash_table) list) : value =
   case bop of
      BOP_PLUS => 
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => VALUE_NUMBER (n1+n2)
            |  (VALUE_STRING s1, VALUE_STRING s2) => VALUE_STRING (s1^s2)
            |  _ => raise AddException (map_value_to_string lft, map_value_to_string rht))
         end
   |  BOP_MINUS =>
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => VALUE_NUMBER (n1-n2)
            |  _ => raise ArithmeticException (BOP_MINUS, map_value_to_string lft, map_value_to_string rht))
         end
   |  BOP_TIMES =>
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => VALUE_NUMBER (n1*n2)
            |  _ => raise ArithmeticException (BOP_TIMES, map_value_to_string lft, map_value_to_string rht))
         end
   |  BOP_DIVIDE =>
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => 
                  if n2 = 0
                  then raise ZeroDivideException
                  else VALUE_NUMBER (n1 div n2)
            |  _ => raise ArithmeticException (BOP_DIVIDE, map_value_to_string lft, map_value_to_string rht))
         end
   |  BOP_MOD => 
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => VALUE_NUMBER (n1 mod n2)
            |  _ => raise ArithmeticException (BOP_MOD, map_value_to_string lft, map_value_to_string rht))
         end
   |  BOP_EQ =>
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of 
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => VALUE_BOOL (n1 = n2)
            |  (VALUE_STRING s1, VALUE_STRING s2) => VALUE_BOOL (s1 = s2)
            |  (VALUE_BOOL b1, VALUE_BOOL b2) => VALUE_BOOL (b1 = b2)
            |  (VALUE_NONE, VALUE_NONE) => VALUE_BOOL true
            |  (CLOSURE c1, CLOSURE c2) => VALUE_BOOL (#3 c1 = #3 c2)
            |  (METHOD (mo1, mc1), METHOD (mo2, mc2)) => (
                  case (mo1, mc2, mo2, mc2) of
                     (VALUE_OBJECT o1, CLOSURE c1, VALUE_OBJECT o2, CLOSURE c2) => 
                        VALUE_BOOL ((#3 o1 = #3 o2) andalso (#3 c1 = #3 c2))
                  |  _ => VALUE_BOOL false
            )
            |  (VALUE_OBJECT o1, VALUE_OBJECT o2) => VALUE_BOOL (#3 o1 = #3 o2)
            |  _ => VALUE_BOOL false)
         end
   |  BOP_NE => 
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of 
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => VALUE_BOOL (n1 <> n2)
            |  (VALUE_STRING s1, VALUE_STRING s2) => VALUE_BOOL (s1 <> s2)
            |  (VALUE_BOOL b1, VALUE_BOOL b2) => VALUE_BOOL (b1 <> b2)
            |  (VALUE_NONE, VALUE_NONE) => VALUE_BOOL false
            |  (CLOSURE c1, CLOSURE c2) => VALUE_BOOL (#3 c1 <> #3 c2)
            |  (METHOD (mo1, mc1), METHOD (mo2, mc2)) => (
                  case (mo1, mc2, mo2, mc2) of
                     (VALUE_OBJECT o1, CLOSURE c1, VALUE_OBJECT o2, CLOSURE c2) => 
                        VALUE_BOOL ((#3 o1 <> #3 o2) orelse (#3 c1 <> #3 c2))
                  |  _ => VALUE_BOOL false
            )
            |  (VALUE_OBJECT o1, VALUE_OBJECT o2) => VALUE_BOOL (#3 o1 <> #3 o2)
            |  _ => VALUE_BOOL true)
         end
   |  BOP_LT => 
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => VALUE_BOOL (n1 < n2)
            |  _ => raise RelationalException (BOP_LT,  map_value_to_string lft, map_value_to_string rht))
         end
   |  BOP_GT =>
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => VALUE_BOOL (n1 > n2)
            |  _ => raise RelationalException  (BOP_GT,  map_value_to_string lft, map_value_to_string rht))
         end
   |  BOP_LE =>
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => VALUE_BOOL (n1 <= n2)
            |  _ => raise RelationalException (BOP_LE,  map_value_to_string lft, map_value_to_string rht))
         end
   |  BOP_GE =>
         let
           val lft = evaluate_expression lftexp states
           val rht = evaluate_expression rhtexp states
         in
            (case (lft, rht) of
               (VALUE_NUMBER n1, VALUE_NUMBER n2) => VALUE_BOOL (n1 >= n2)
            |  _ => raise RelationalException (BOP_GE,  map_value_to_string lft, map_value_to_string rht))
         end
   |  BOP_AND =>   
         let
           val lft = evaluate_expression lftexp states
         in
            (case lft of 
               (VALUE_BOOL b1) =>
                  if b1
                  then 
                     let
                       val rht = evaluate_expression rhtexp states
                     in
                       (case rht of 
                        (VALUE_BOOL b2) =>
                           VALUE_BOOL b2
                        |  _ => raise BooleanSecondException (BOP_AND, map_value_to_string rht))
                     end
                  else VALUE_BOOL false
            |  _ => raise BooleanFirstException (BOP_AND,  map_value_to_string lft))
         end
   |  BOP_OR =>
         let
           val lft = evaluate_expression lftexp states
         in
            (case lft of 
               (VALUE_BOOL b1) =>
                  if b1
                  then VALUE_BOOL true
                  else
                     let
                       val rht = evaluate_expression rhtexp states
                     in
                       (case rht of 
                        (VALUE_BOOL b2) =>
                           VALUE_BOOL b2
                        |  _ => raise BooleanSecondException (BOP_OR, map_value_to_string rht))
                     end
            |  _ => raise BooleanFirstException (BOP_OR,  map_value_to_string lft))
         end

and evaluate_unary_op (uop : unaryOperator) (v : value) : value =
   case uop of
      UOP_NOT =>
         (case v of 
            VALUE_BOOL b => VALUE_BOOL (not b)
         |  _ => raise UnaryNotException  (map_value_to_string v)
         )
   |  UOP_MINUS =>
         (case v of 
            VALUE_NUMBER n => VALUE_NUMBER (n * ~1)
         |  _ => raise UnaryMinusException  (map_value_to_string v)
         )

and evaluate_expression (exp : expression) (states :  ((string, value) hash_table) list) : value =
   case exp of 
      EXP_ID eid => 
         search_states (states, eid)
   |  EXP_NUM i => VALUE_NUMBER i
   |  EXP_STRING s => VALUE_STRING s 
   |  EXP_BOOL b => VALUE_BOOL b
   |  EXP_NONE => VALUE_NONE
   |  EXP_BINARY {opr, lft, rht} => evaluate_binary_op opr lft rht states
   |  EXP_UNARY {opr, opnd} => 
      let
        val eopnd = evaluate_expression opnd states
      in
        evaluate_unary_op opr eopnd
      end
   |  EXP_COND {guard, thenExp, elseExp} =>
      let
         val guardresult = evaluate_expression guard states
      in
         case guardresult of
            VALUE_BOOL b =>
               if b
               then evaluate_expression thenExp states
               else evaluate_expression elseExp states
         |  _ => raise ConditionalException (map_value_to_string guardresult)
      end
   |  EXP_ASSIGN {lhs, rhs} => 
         let
           val erhs = evaluate_expression rhs states
         in
           (case lhs of 
               EXP_ID eid => search_states_assign (states, eid, erhs)
            |  EXP_DOT {obj, field} => (
                  let
                     val eobj = evaluate_expression obj states
                  in
                     case eobj of 
                           VALUE_OBJECT (c, h, u) => 
                              let
                                 val fieldexists = search_states (h, field) handle (UndeclaredVariableException _) => raise FieldNotFoundException (field)
                              in
                                 search_states_assign (h, field, erhs)
                              end
                        |  _ => raise FieldSetNonObjectException (field, map_value_to_string eobj)
                  end
            )
            )
         end
   | EXP_CALL {func, args} => 
      let
        val efunc = evaluate_expression func states
        val eargs = evaluate_args (states, args)
        val newstate : (string,value) hash_table = mkTable (hash_fn, cmp_fn) (initial_size, UndeclaredVariableAssignmentException "Variable undeclared");
      in
         case efunc of 
            CLOSURE ({params, decls, body}, s, u) => 
               (evaluate_ids (decls, newstate);
               (evaluate_statement_list body (evaluate_func_params (newstate::s, params, eargs))) handle ReturnException v => v)
         |  METHOD (obj, c) =>
            (case (obj, c) of 
               (VALUE_OBJECT vo, CLOSURE cv) => 
                  (
                     insert newstate ("this", obj);
                     (evaluate_ids (#decls (#1 cv), newstate);
                     (evaluate_statement_list (#body (#1 cv)) (evaluate_func_params (newstate :: ((#2 vo) @ (#2 cv)), (#params(#1 cv)), eargs))) handle ReturnException v => v)
                  )
               | _ => raise NonFunctionException (map_value_to_string efunc)
            )
         |  _ => raise NonFunctionException (map_value_to_string efunc)
      end
   | EXP_ANON {params, decls, body} => CLOSURE ({params=params, decls=decls, body=body}, states, ref ())
   | EXP_NEW {class} => evaluate_new_exp class states 
   | EXP_THIS => search_states (states, "this")
   | EXP_DOT {obj, field} => 
      let
        val eobj = evaluate_expression obj states
      in
        case eobj of 
            VALUE_OBJECT (c, h, u) => 
               let
                 val objfield = search_states (h, field) handle (UndeclaredVariableException _) => raise FieldNotFoundException (field)
               in
                 case objfield of 
                     CLOSURE(fdef, vars, un) => 
                        (
                           METHOD(eobj, CLOSURE(fdef, vars, un))
                        )
                  |  _ => objfield
               end
         |  _ => raise FieldGetNonObjectException (field, map_value_to_string eobj)
      end

and evaluate_args (states : ((string,value) hash_table) list, args : expression list) : value list =
   case args of
      [] => []
   |  x::xs => 
      (evaluate_expression x states) :: (evaluate_args (states, xs))
and evaluate_statement (stmt : statement) (states : ((string,value) hash_table) list) : unit =
   case stmt of 
      ST_EXP {exp} => (evaluate_expression exp states;
                        ())
   |  ST_BLOCK {stmts} =>
         ( case stmts of
               [] => ()
            |  x::xs =>
                  (evaluate_statement x states;
                  evaluate_statement (ST_BLOCK {stmts=xs}) states;
                  ())
         )
   |  ST_IF {guard, th, el} =>
         let
           val evalguard = evaluate_expression guard states
         in
           (case evalguard of 
               VALUE_BOOL b => (
                  if b
                  then evaluate_statement th states
                  else 
                     if (Option.isSome el)
                     then (evaluate_statement (Option.valOf el) states)
                     else ()
               )
            |   _ => raise IfGuardException (map_value_to_string evalguard)
           )
         end
   |  ST_PRINT {exp} =>
         let
           val printeval = evaluate_expression exp states
         in
           (print (print_value_to_string printeval);
           ())
         end
   |  ST_WHILE {guard, body} =>
         let
           val guardval = evaluate_expression guard states
         in
           (case guardval of
               VALUE_BOOL b =>
                  (if b
                  then (
                     evaluate_statement body states;
                     evaluate_statement stmt states)
                  else ())
            |   _ => raise WhileGuardException (map_value_to_string guardval))
         end
   | ST_RETURN {exp} => 
      if List.length states = 1
      then raise ReturnOutsideFunctionException
      else(
         case exp of 
            NONE => raise ReturnException VALUE_NONE
         |  SOME foo => raise ReturnException (evaluate_expression foo states))

and evaluate_func_params (states : ((string,value) hash_table) list, decls : decl list, args : value list) : ((string,value) hash_table) list =
   case (decls, args) of 
      ([], []) => states
   |  ([], x::xs) => raise CallTooManyArgumentsException
   |  (x::xs, []) => raise CallTooFewArgumentsException
   |  (x::xs, y::ys) => (
         let
           val statetable = hd states
           val v = find statetable x
         in
           case v of 
               SOME _ => raise VariableRedeclarationException x
            |  NONE => insert statetable (x, y);
            evaluate_func_params (states, xs, ys)
         end
   )

and evaluate_statement_list (stmtlist : statement list) (states : ((string,value) hash_table) list) : value =
   case stmtlist of 
      [] => VALUE_NONE
   |  x::xs =>
         (evaluate_statement x states;
         evaluate_statement_list xs states)
;

fun cleanup_helper(classlist : string list) : unit =
   case classlist of 
      [] => ()
   |  x::xs => 
         case find namespace x of 
            NONE => (
            (cleanup_helper xs); 
            ())
         | SOME v => ((remove namespace x);
            (cleanup_helper xs); 
            ())
;

fun cleanup () : unit =
   let
     val classlist = find prev_classes "old"
   in
      case classlist of 
         NONE => ()
      |  SOME v => 
         ( 
         cleanup_helper v;
         ()
         )
   end
;

fun evaluate (prgrm : program) : unit =
   let
      val state : (string, value) hash_table = mkTable (hash_fn, cmp_fn) (initial_size, UndeclaredVariableAssignmentException "Variable undeclared");
   in
      case prgrm of
         PROGRAM {classes, decls, funcs, stmts} =>
            (
            (cleanup());
            (insert prev_classes ("old", []));
            evaluate_classes classes namespace;
            evaluate_ids (decls, state);
            evaluate_func_decls (funcs, [state]);
            evaluate_statement_list stmts [state];
            ())
   end 
;