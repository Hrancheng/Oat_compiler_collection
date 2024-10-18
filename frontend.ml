open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements that will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

(* The type of streams of LLVMLite instructions. Note that to improve performance,
 * we will emit the instructions in reverse order. That is, the LLVMLite code:
 *     %1 = mul i64 2, 2
 *     %2 = add i64 1, %1
 *     br label %l1
 * would be constructed as a stream as follows:
 *     I ("1", Binop (Mul, I64, Const 2L, Const 2L))
 *     >:: I ("2", Binop (Add, I64, Const 1L, Id "1"))
 *     >:: T (Br "l1")
 *)
type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearerhw, I may do that for next time around.]]

 
   Consider globals7.oat (in hw4programs)

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: to compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]




(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)

(*HERE IS HELPER FUNCTIONS FOR cmp_exp*)
let int64_of_bool b = if b then 1L else 0L



let bop_to_ll_bop (b: Ast.binop) : Ll.bop = 
  begin match b with 
  | Add -> Ll.Add
  | Sub -> Ll.Sub
  | Mul -> Ll.Mul
  | And -> Ll.And
  | Or -> Ll.Or
  | IAnd -> Ll.And
  | IOr -> Ll.Or
  | Shl -> Ll.Shl
  | Shr -> Ll.Lshr
  | Sar -> Ll.Ashr
  | _ -> failwith "unexpected type"
  end

let bop_to_ll_cnd (b: Ast.binop) : Ll.cnd = 
  begin match b with 
  | Eq -> Ll.Eq
  | Neq -> Ll.Ne
  | Lt -> Ll.Slt
  | Lte -> Ll.Sle
  | Gt -> Ll.Sgt
  | Gte -> Ll.Sge
  | _ -> failwith "unexpected type"
  end

(*type binop =
| Add
| Sub
| Mul
| Eq
| Neq
| Lt
| Lte
| Gt
| Gte
| And
| Or
| IAnd
| IOr
| Shl
| Shr
| Sar*)

(*type unop =
| Neg
| Lognot
| Bitnot
*)
let rec type_translate_for_Bop_Uop (exp: Ast.exp) : Ast.ty = 
  begin match exp with 
  | Bop (b, _, _) ->
    begin match b with 
    | Add | Sub | Mul | IAnd | IOr | Shl | Shr | Sar -> TInt
    | Eq | Neq | Lt | Gt | Lte | Gte | And | Or -> TBool
    end
  | Uop (u, _) ->
    begin match u with
    | Neg | Bitnot -> TInt
    | Lognot -> TBool
    end
  | _ -> failwith "wrong"
  end

  let value_loading (type_op_stream: Ll.ty * Ll.operand * stream) : Ll.ty * Ll.operand * stream =
    let (operand_type, operand, code_stream) = type_op_stream in
    match (operand_type, operand) with
    | (Ptr ptr_type, Gid global_id) ->
    (*Global string needs bitcast. pointer to an array -> pointer to the first element
       of an array*) 
      begin match ptr_type with
      | Array (size, I8) -> (*operand points to an array of i8, as well as string*)
        let string_cast_id = gensym "str_cast" in
        let cast_code = [E (string_cast_id, Bitcast(Ptr operand_type, Gid global_id, Ptr I8))] in
        (Ptr I8, Id string_cast_id, code_stream @ cast_code)
      | _ -> (*operand points to an array not of i8. Normal array not necessary to bitcast*)
        let load_id = gensym "load_global" in
        let load_code = [I (load_id, Load(Ptr operand_type, Gid global_id))] in
        (operand_type, Id load_id, code_stream @ load_code)
      end
  
    | (Ptr ptr_type, _) -> (*not point to global, non global string does not need bitcast*)
    (*not global string -> malloc, was assigned i8* but not [i8, n*i8]*  *)
      let load_id = gensym "load_ptr" in
      let load_code = [I (load_id, Load(operand_type, operand))] in
      (ptr_type, Id load_id, code_stream @ load_code)
  
    | _ -> 
      type_op_stream
  
  let cmp_uop (b: Ast.unop) (op: Ll.operand) (t: Ll.ty) : Ll.insn =
    begin match b with 
    | Lognot -> Ll.Binop (Ll.Xor, t, op, Ll.Const (1L))
    | Neg -> Ll.Binop (Ll.Mul, t, op, Ll.Const (-1L))
    | Bitnot -> Ll.Binop (Ll.Xor, t, op, Ll.Const (-1L))
    end
let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | CNull t -> (cmp_rty t, Ll.Null,[])
  | CBool b -> (Ll.I1, Ll.Const (int64_of_bool b),[])
  | CInt i -> (Ll.I64, Ll.Const i,[])
  | CStr s -> 
    let str_len = String.length s + 1 in
    let arr_ty = Ll.Array (str_len, Ll.I8) in
    let str_gid = gensym "str_global" in
    let str_ptr_id = gensym "str_ptr" in
    let global_decl = G(str_gid, (arr_ty, GString s)) in
    let gep_instr = I(str_ptr_id, Gep(Ptr arr_ty, Gid str_gid, [Const 0L; Const 0L])) in
    (Ptr I8, Id str_ptr_id, [global_decl; gep_instr])  
  | Bop (b, e1, e2) ->
    let t1, op1, st_for_e1 = value_loading @@ cmp_exp c e1 in
    let _, op2, st_for_e2 = value_loading @@ cmp_exp c e2 in

    let t = type_translate_for_Bop_Uop (Bop (b, e1, e2)) in 
    let id = gensym "bop" in
    
    begin match b with
    | Add | Sub | Mul | IAnd | IOr | Shl | Shr | Sar | And | Or -> 
      (cmp_ty t, Ll.Id id, st_for_e1 >@ st_for_e2 >@ [I (id, Ll.Binop (bop_to_ll_bop b, t1, op1, op2))])
    | Eq | Neq | Lt | Lte | Gt | Gte  ->
      (cmp_ty t, Ll.Id id, st_for_e1 >@ st_for_e2 >@ [I (id, Ll.Icmp (bop_to_ll_cnd b, t1, op1, op2))])
    end
  | Id(id) -> 
    let uid = gensym "id_load" in
    let (t, op) = Ctxt.lookup id c in
    begin match t with
    | Ptr(Array(s, elem_ty)) -> 
      let cast_ty = Ptr elem_ty in
      let cast_instr = I(uid, Bitcast(t, op, cast_ty)) in
      (cast_ty, Id(uid), [cast_instr])
    | Ptr(Struct([I64; Array(_, arr_ty)])) -> 
      let new_struct_ty = Ptr(Struct([I64; Array(0, arr_ty)])) in
      let cast_instr = I(uid, Bitcast(t, op, new_struct_ty)) in
      (new_struct_ty, Id(uid), [cast_instr])
    | Ptr(elem_ty) -> 
      let load_instr = I(uid, Load(t, op)) in
      (elem_ty, Id(uid), [load_instr])
    | _ -> 
      failwith "must be ptr type"
    end
  | Uop (uop1, e1) -> 
    let t = type_translate_for_Bop_Uop (Uop (uop1, e1)) in 
    let id = gensym "uop" in
    let ty, op, st = value_loading @@ cmp_exp c e1 in
    (cmp_ty t, Ll.Id id, st >@ [I (id, cmp_uop uop1 op ty)])
  | Call(f, args) -> (
    let f_ty_pointer, f_op = match f.elt with
      | Id(id) -> Ctxt.lookup id c
      | _ -> 
        let ty, op, _ = cmp_exp c f in
        match ty with
        | Ptr Fun(_, _) -> ty, op
        | _ -> failwith "call must be pointer"
    in
    match f_ty_pointer with
    | Ptr Fun(_, ret_ty) -> 
      let args_and_strs = List.map (cmp_exp c) args in
      let ll_args = List.map (fun (ty, op, _) -> (ty, op)) args_and_strs in
      let strs = List.concat (List.map (fun (_, _, str) -> str) args_and_strs) in
      let uid = gensym "" in
      let call: Ll.insn = Call(ret_ty, f_op, ll_args) in
      ret_ty, Id(uid), strs >:: I(uid, call)
    | _ -> failwith "f must be ptr fun"
  )
  | NewArr (t, e_node) ->
    let _, exp_op, e_st = cmp_exp c e_node in
    let arr_t, arr_op, arr_st = oat_alloc_array t exp_op in
    (arr_t, arr_op, e_st >@ arr_st)
  | Index(e1, e_index) -> (
      let arr_ty, arr_op, arry_str = cmp_exp c e1 in
      let _, index_op, index_str = cmp_exp c e_index in
      match arr_ty with
      | Ptr(Struct [_; Array(_, ty)]) ->
        let pointer_id = gensym "pointer_id" in
        let value_id = gensym "value_id" in
        ty, Id(value_id), arry_str >@ index_str >:: I(pointer_id, Gep(arr_ty, arr_op, 
        [Const(Int64.zero); Const(Int64.one); index_op])) >:: I(value_id, Load(Ptr(ty), Id pointer_id))
      | _ -> failwith "have to be ptr for e1 of index")
  | CArr (typ, e_node_list) ->
    let arr_len = Ll.Const (Int64.of_int (List.length e_node_list)) in
    let arr_t, arr_op, arr_st = oat_alloc_array typ arr_len in 
    let streams = List.mapi (fun i el ->
        let index_op = Ll.Const (Int64.of_int i) in
        let el_ty, el_op, el_st = cmp_exp c el in
        let arr_el_id = gensym "arr_el_gep" in 
        el_st 
        >@ [I (arr_el_id, Ll.Gep (arr_t, arr_op, [Ll.Const 0L; Ll.Const 1L; index_op]))]
        >@ [I (arr_el_id, Ll.Store (el_ty, el_op, Ll.Id arr_el_id))]
      ) e_node_list in
    (arr_t, arr_op, arr_st >@ List.concat streams)
   


(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)

 (*HERE IS HELPER FUNCTION FOR cmp_stmt*)
 let load_value_if_needed (ty: Ll.ty) (operand: Ll.operand) : Ll.operand * stream =
  match ty, operand with
  | Ptr p, _ -> 
    let loaded_id = gensym "loaded_val" in
    let load_instr = I(loaded_id, Ll.Load(p, operand)) in
    (Ll.Id loaded_id, [load_instr])
  | _, Gid g -> 
    let casted_id = gensym "casted" in
    let cast_instr = I(casted_id, Ll.Bitcast(ty, operand, Ptr I8)) in
    (Ll.Id casted_id, [cast_instr])
  | _, _ -> (operand, [])

let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with
  | Decl (e1, e2) ->
    let var_type, init_op, init_code = cmp_exp c e2 in
    let var_alloc_id = gensym ("alloc_" ^ e1) in
    let updated_context = Ctxt.add c e1 (Ptr var_type, Id var_alloc_id) in
    (updated_context, init_code @ [E (var_alloc_id, Alloca var_type)] @ 
    [I ("store_" ^ e1, Store (var_type, init_op, Id var_alloc_id))])
  | SCall(f, arg_li) ->
    let _, _, st = cmp_exp c (no_loc (Call(f, arg_li)))  in
    c, st
    | While (e_cond, block) ->
      let ty, while_opr, while_strm = cmp_exp c e_cond in
      begin match ty with
      | Ll.I1 ->
        let _, cmp_while_block = cmp_block c ty block in
        let l0 = gensym "begin_while" in
        let l1 = gensym "while_block" in
        let l2 = gensym "end_while" in
        let new_op, load_strm = load_value_if_needed ty while_opr in
        let strm = [T (Br l0)]
                  >@ [L l0]
                  >@ while_strm
                  >@ load_strm
                  >@ [T (Ll.Cbr (new_op, l1, l2))]
                  >@ [L l1]
                  >@ cmp_while_block
                  >@ [T (Br l0)]
                  >@ [L l2] in
        (c, strm)
      | _ -> failwith "must be bool"
      end
  | For(e_dec, e_cond, stmt_list, stmts) ->
    let c, vdecls_str = 
      let rec compile_vdecls c acc = function
        | [] -> (c, acc)
        | vdecl :: rest ->
          let (c, str) = cmp_stmt c rt (no_loc (Decl vdecl)) in
          compile_vdecls c (acc >@ str) rest
      in
      compile_vdecls c [] e_dec
    in

    let cond = match e_cond with
      | Some exp -> exp
      | None -> no_loc (CBool true)
    in
    let st_list = match stmt_list with 
      | Some stmt -> [stmt]
      | None -> []
    in

    let while_stmt = While(cond, (stmts @ st_list)) in
    let c, full_str = cmp_stmt c rt {elt = while_stmt; loc = stmt.loc} in
    (c, vdecls_str >@ full_str)
  
  | Assn(l, r) ->
    let (r_ty, r_op, r_stream) = cmp_exp c r in
    begin match l.elt with
    | Id(id) ->
        let _, dest_op = Ctxt.lookup id c in
        (c, r_stream >:: I (gensym "store", Store(r_ty, r_op, dest_op)))

  | Index(e1, e2) ->
      let arr_ty, arr_op, arr_str = cmp_exp c e1 in
      let _, index_opr, index_str = cmp_exp c e2 in
      begin match arr_ty with
      | Ptr(Struct [_; Array(_, ty)]) ->
          let ptr_id = gensym "ptr" in
          let store_id = gensym "store" in
          (c, r_stream >@ arr_str >@ index_str >::
              I (ptr_id, Gep(arr_ty, arr_op, [Const 0L; Const 1L; index_opr])) >::
                I (store_id, Store(r_ty, r_op, Id ptr_id)))
      | _ -> failwith "first element of array must be of type ptr"
      end

  | _ -> failwith "wrong type"
    end
  
    | If (e_con, then_, else_) ->
      let cond_type, cond_operand, initial_stream = cmp_exp c e_con in
      let _, then_stream = cmp_block c rt then_ in
      let _, else_stream = cmp_block c rt else_ in
      let start_label = gensym "start_if" in
      let true_label = gensym "true_branch" in
      let false_label = gensym "false_branch" in
      let end_label = gensym "end_if" in
  
      let checked_operand, more_stream =
        match cond_type, cond_operand with
        | (Ptr pointer_type, _) -> 
          let _, new_operand, new_stream = 
          value_loading (cond_type, cond_operand, []) in (new_operand, new_stream)
        | (_, Gid global_id) -> 
          let _, new_operand, new_stream = 
          value_loading (cond_type, cond_operand, []) in (new_operand, new_stream)
        | (_, _) -> 
          (cond_operand, [])
      in
  
      let final_stream = initial_stream
        >@ [T (Br start_label)]
        >@ [L start_label]
        >@ more_stream
        >@ [T (Cbr (checked_operand, true_label, false_label))]
        >@ [L true_label]
        >@ then_stream
        >@ [T (Br end_label)]
        >@ [L false_label]
        >@ else_stream
        >@ [T (Br end_label)]
        >@ [L end_label]
      in
      (c, final_stream)
  
  
  | Ret e -> 
    begin match e with
    | None -> 
        (c, [T (Ret (Void, None))])
    | Some re -> 
        let ret_ty, ret_op, ret_code = cmp_exp c re in
        (c, ret_code >:: T (Ret (ret_ty, Some ret_op)))
    end


(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts



(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  let rec update_ctxt c decls =
    match decls with
    | Gvdecl { elt } :: rest -> (
        let { name; init } = elt in
        let init_ty = init.elt in
        let ty = match init_ty with
          | CArr (e_ty, elems) -> Ptr (Struct [I64; Array(List.length elems, cmp_ty e_ty)])
          | CInt i        -> Ptr I64
          | CBool b       -> Ptr I1
          | CStr s        -> Ptr (Array (1 + String.length s, I8))
          | CNull rty     -> Ptr(Ptr (cmp_rty rty))
          | _ -> failwith "wrong type for global"
        in
        update_ctxt (Ctxt.add c name (ty, Gid name)) rest
      )
    | [] -> c
    | _ :: rest -> update_ctxt c rest
  in
  update_ctxt c p

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)
let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let fd = f.elt in
  let param_types = List.map (fun (ty, _) -> cmp_ty ty) fd.args in
  let ret_type = cmp_ret_ty fd.frtyp in
  let f_ty = (param_types, ret_type) in
  let f_params = List.map snd fd.args in

  let ctxt, param_code = 
    let rec process_params ctxt code params =
      match params with
      | [] -> (ctxt, code)
      | (ty, id)::rest ->
        let uid = gensym id in
        let ini_store_id = gensym "store" in
        let llvm_ty = cmp_ty ty in
        let new_ctxt = Ctxt.add ctxt id (Ptr llvm_ty, Id uid) in
        let new_code = code >:: E(uid, Alloca llvm_ty) >:: I(ini_store_id, Store(llvm_ty, Id id, Id uid)) in
        process_params new_ctxt new_code rest
    in
    process_params c [] fd.args
  in

  let block_code = cmp_block ctxt ret_type fd.body in
  let (f_cfg, global_decls) = cfg_of_stream (param_code >@ snd block_code) in

  ({f_ty; f_param = f_params; f_cfg}, global_decls)


(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)
let rec cmp_gexp c (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CInt i ->  (I64, GInt i), []
  | CStr s ->  (Array (1 + String.length s, I8), GString s), []

  | CArr (e_ty, e2) ->
    let num = List.length e2 in
    let llvm_elem_type = 
      begin match e_ty with
      | TRef (RString) -> Ll.Array (num + 1, Ll.I8)
      | _ -> cmp_ty e_ty
      end
    in
    let llvm_arr_type = Ll.Struct ([Ll.I64; (Ll.Array (num, llvm_elem_type))]) in
    let length_element = [ (Ll.I64, Ll.GInt (Int64.of_int @@ num)) ] in
    
    let rec process_elements elements index acc =
      match elements with
      | [] -> acc
      | el::rest ->
        let el_gdecl, _ = cmp_gexp c el in
        process_elements rest (index + 1) (acc @ [el_gdecl])
    in
    let element_gdecls = process_elements e2 0 [] in
    
    let arr_gdecl = (llvm_arr_type, Ll.GStruct [(Ll.I64, Ll.GInt (Int64.of_int num)); (Ll.Array (num, llvm_elem_type), Ll.GArray element_gdecls)]) in
    
    (arr_gdecl, [])

  | CNull t -> ((Ptr(cmp_rty t), Ll.GNull),[])
  | CBool b ->  (I1, GInt(int64_of_bool b)), []
  | _ -> failwith "wrong type"



(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
