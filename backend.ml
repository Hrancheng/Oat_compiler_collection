(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

module Platform = Util.Platform

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins =
  function
    | Null ->
        (Movq, [Imm (Lit 0L); dest])
    | Const i ->
        (Movq, [Imm (Lit i); dest])
    | Gid gid ->
        (Leaq, [Ind3 (Lbl (Platform.mangle gid), Rip); dest])
    | Id uid ->
        let x86_oprand_ = (lookup ctxt.layout uid) in
        (Movq, [x86_oprand_; dest])



(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)
let arg_to_reg (n : int) : operand =
  match n with
  | 0 -> Reg Rdi
  | 1 -> Reg Rsi
  | 2 -> Reg Rdx
  | 3 -> Reg Rcx
  | 4 -> Reg R08
  | 5 -> Reg R09
  | _ -> Reg Rax


let compile_call (ctxt : ctxt) (fn : Ll.operand) (args : (Ll.ty * Ll.operand) list) (dest : X86.operand) : ins list =
  (*first compute the number of args put on stack*)
  let stack_arg_count = if List.length args > 6 then List.length args - 6 else 0 in
  (*second to move arguments to register or stack*)
  (*third to add RSP to allocate space*)
  let arg_operation ctxt i arg = 
    let ins = compile_operand ctxt (arg_to_reg i) arg in
    match i with
    | 0 -> [ins]
    | 1 -> [ins]
    | 2 -> [ins]
    | 3 -> [ins]
    | 4 -> [ins]
    | 5 -> [ins]
    | _ -> (compile_operand ctxt (arg_to_reg i) arg) :: [(Pushq, [arg_to_reg i])] in
  let move_args_to_regs = List.mapi (fun i (_, arg) -> arg_operation ctxt i arg) args |> List.flatten in
  (*fourth to move the result to dest*)
  (*fifth to resume the stack*)
  let ins_last : ins = (Addq, [Imm (Lit (Int64.of_int (8*stack_arg_count))); Reg Rsp]) in
  move_args_to_regs @ compile_operand ctxt (Reg Rax) fn :: 
  [(Callq, [Reg Rax])] @ ((Movq, [Reg Rax; dest]) :: [ins_last])




(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int =
  match t with 
  | Void | I8 | Fun _ -> 0
  | I1 | I64 | Ptr _ -> 8
  | Struct ts -> List.fold_left (fun acc t -> acc + size_ty tdecls t) 0 ts
  | Array (n, t_) -> n * size_ty tdecls t_
  | Namedt tid -> size_ty tdecls (lookup tdecls tid)




(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)


let add_n_ty_from_struct ctxt n s : int =
  let rec add_n_ty_from_struct' n s = 
    match s with
    | [] -> 0
    | ty :: s' -> 
      if n = 0 then 0
      else size_ty ctxt.tdecls ty + add_n_ty_from_struct' (n-1) s'
  in
  add_n_ty_from_struct' n s
  

let rec rec_helper (ctxt:ctxt) (ty : Ll.ty) (path : Ll.operand list) : ins list =
begin match path with
  | op :: tail ->
    begin match ty with
      | Namedt tid -> rec_helper ctxt (lookup ctxt.tdecls tid) path
      | Array (n, ty) -> 
        let size_of_ty = Int64.of_int (size_ty ctxt.tdecls ty) in
          compile_operand ctxt (Reg Rcx) op :: (Imulq, [Imm (Lit size_of_ty); Reg Rcx]) 
          :: (Addq, [Reg Rcx; Reg Rax]) :: rec_helper ctxt ty tail
      | (Struct str) ->
        begin match op with
          | Const num ->
            let ty = List.nth str (Int64.to_int num) in
            let struct_size = add_n_ty_from_struct ctxt (Int64.to_int num) str in
              (Addq, [Imm (Lit (Int64.of_int struct_size)); Reg Rax]) :: rec_helper ctxt ty tail
          | _ -> failwith "wrong type for ptr operand"
        end
      | _ -> failwith "wrong type for actual operand"
    end
    | _ -> []
  end


let compile_gep (ctxt:ctxt) (op : Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
let (ptr,dest) = op in
   match ptr with
    | Ptr ty -> let ins1 = (compile_operand ctxt (Reg Rax) dest) in
                let actual_ty = Array (7, ty) in
               let ins2 = rec_helper ctxt actual_ty path
             in
            [ins1] @ ins2
    | _ -> failwith "not pointer type"



(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  begin match i with
  | Binop (bop, ty, op1, op2) -> 
    (*define i64 @main(i64 %argc, i8** %arcv) {
  %1 = add i64 5, 9
  ret i64 %1
  }
  *)
    let dest = Reg Rax in
    let ins1 = compile_operand ctxt (Reg Rax) op1 in
    let ins2 = compile_operand ctxt (Reg Rcx) op2 in
    let ins3 = 
      match bop with
      | Add -> (Addq, [Reg Rcx; dest])
      | Sub -> (Subq, [Reg Rcx; dest])
      | Mul -> (Imulq, [Reg Rcx; dest])
      | Shl -> (Shlq, [Reg Rcx; dest])
      | Lshr -> (Shrq, [Reg Rcx; dest])
      | Ashr -> (Sarq, [Reg Rcx; dest])
      | And -> (Andq, [Reg Rcx; dest])
      | Or -> (Orq, [Reg Rcx; dest])
      | Xor -> (Xorq, [Reg Rcx; dest])
    in
    let ins4 =
      (Movq, [dest; (lookup ctxt.layout uid)]) in
    [ins1; ins2; ins3; ins4]
    | Alloca (ty) ->
      let dest = Reg Rax in
      let ty_size = size_ty ctxt.tdecls ty in
      let ins1 = (Subq, [Imm (Lit (Int64.of_int ty_size)); Reg Rsp]) in
      let ins2 = (Movq, [Reg Rsp; dest]) in
      let ins3 =
        (Movq, [dest; (lookup ctxt.layout uid)]) in
      [ins1; ins2; ins3]
      | Load (ty, op) ->
        let dest = Reg Rcx in
        let ins1 = compile_operand ctxt dest op in
        let ins2 = (Movq, [Ind2 Rcx; Reg Rax]) in
        let ins3 =
          (Movq, [Reg Rax; (lookup ctxt.layout uid)]) in
        [ins1; ins2; ins3]
      | Store (ty, op1, op2) ->
        let ins1 = compile_operand ctxt (Reg Rax) op1 in
        let ins2 = compile_operand ctxt (Reg Rdx) op2 in
        let ins3 = (Movq, [Reg Rax; Ind2 (Rdx)]) in
        [ins1; ins2; ins3]
      | Icmp (cond, ty, op1, op2) ->
        let dest = Reg Rax in
        let ins1 = compile_operand ctxt (Reg Rax) op1 in
        let ins2 = compile_operand ctxt (Reg Rdx) op2 in
        let ins3 = (Cmpq, [Reg Rdx; Reg Rax]) in
        let ins4 = (Set (compile_cnd cond), [dest]) in
        let ins5 =
          (Movq, [dest; (lookup ctxt.layout uid)]) in
        [ins1; ins2; ins3; ins4; ins5]
    | Call (ty, func, args) -> compile_call ctxt func args (lookup ctxt.layout uid)
    | Bitcast (ty1, op, ty2) ->
      let dest = Reg Rax in
      let ins1 = compile_operand ctxt dest op in
      let ins2 = (Movq, [dest; (lookup ctxt.layout uid)]) in
      [ins1; ins2]
    | Gep (ty, op, ops) -> compile_gep ctxt (ty, op) ops @ [(Movq, [Reg Rax; (lookup ctxt.layout uid)])]
  end



(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are 
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  match t with
  | Ret (_, None) -> (Movq, [Reg Rbp; Reg Rsp]) :: (Popq, [Reg Rbp]) :: [(Retq, [])]
  | Ret (ty_, Some operand_) -> compile_operand ctxt (Reg Rax) operand_ ::
  (Movq, [Reg Rbp; Reg Rsp]) :: (Popq, [Reg Rbp]) :: [(Retq, [])]
  | Br lbl -> [(Jmp, [Imm (Lbl (mk_lbl fn lbl))])]
  | Cbr (op, l1, l2) ->
    compile_operand ctxt (Reg Rax) op ::
    (Cmpq, [Imm (Lit 0L); Reg Rax]) :: 
    (J Neq, [Imm (Lbl (mk_lbl fn l1))]) :: 
    [(Jmp, [Imm (Lbl (mk_lbl fn l2))])]


(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. 
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  match blk with
  | {insns; term} ->
    let insns = List.map (fun insn -> compile_insn ctxt insn) insns |> List.flatten in
    let term = compile_terminator fn ctxt (snd term) in
    insns @ term


let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
  match n with
  | 0 -> Reg Rdi
  | 1 -> Reg Rsi
  | 2 -> Reg Rdx
  | 3 -> Reg Rcx
  | 4 -> Reg R08
  | 5 -> Reg R09
  | _ -> 
    let offset = Int64.of_int ((n - 6 + 2) * 8)
    in Ind3 (Lit offset, Rbp) 


(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)
let generate_instructions f_param : ins list =
  List.mapi (fun n uid ->
    (Pushq, [arg_loc n])
  ) f_param

let count_uids_in_block block =
  let count_insns = List.length block.insns in
  let count_term = 1 in
  count_insns + count_term

let count_uids_in_cfg cfg =
  let entry_block, labeled_blocks = cfg in
  let count_entry = count_uids_in_block entry_block in
  let count_labeled = List.fold_left (fun acc (_, blk) -> acc + count_uids_in_block blk) 0 labeled_blocks in
  count_entry + count_labeled

let stack_layout (args : uid list) ((block, lbled_blocks):cfg) : layout =
  (*first to compute the number of args*)
  (*second to compute the number of uid in blocks*)
let arg_num = List.length args in
  let block_uid_num =  count_uids_in_block block in
  let arg_layout = List.mapi (fun i uid -> (uid, Ind3 (Lit (Int64.of_int (-(i+1)*8)), Rbp))) args in
  let local_layout = 
    List.mapi (fun i (uid, _) -> 
      (uid, Ind3 (Lit (Int64.mul (-8L) (Int64.of_int (i + arg_num + 1))), Rbp))) block.insns in
  let lbl_local_layout = List.map (fun (lbl, blk) -> 
    List.mapi (fun i (uid, _) -> 
      (uid, Ind3 (Lit (Int64.mul (-8L) 
      (Int64.of_int (i + arg_num + block_uid_num + 1))), Rbp))) blk.insns) 
      lbled_blocks in
  List.flatten (arg_layout :: local_layout :: lbl_local_layout)

(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_param; f_cfg; _ }:fdecl) : prog =
  let (a, b) = f_cfg in
  let uid_num = List.length f_param + count_uids_in_cfg f_cfg in
  let prepare = 
    (Pushq, [Reg Rbp]) :: [(Movq, [Reg Rsp; Reg Rbp])] in
    let prepare = prepare @
    generate_instructions f_param
    @ [(Subq, [Imm (Lit (Int64.mul 8L (Int64.of_int(uid_num)))); Reg Rsp])] in
    let ctxt = { tdecls; layout = stack_layout f_param f_cfg } in
    let ins1 = compile_block name ctxt a in
    let ins2 = List.map (fun (lbl, blk) -> compile_lbl_block name lbl ctxt blk) b in
    let mangled_name =
      Platform.mangle name in
    let elems =
      if name = "main" then
        (* Create the global directive for the main function *)
        let global_directive = Asm.data mangled_name [] in
        let text_elem = Asm.gtext mangled_name (prepare @ ins1) in
        [text_elem] @ ins2
      else
        (* If it's not main, just use the text element *)
        [Asm.text mangled_name (prepare @ ins1)] @ ins2
    in
    
  (* Print the elems list *)
    (* ... *)
  
    elems
  
  (* ... *)



(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (_t1,g,_t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls; _} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
