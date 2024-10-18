(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | _ -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x ->
  match x with
  | Eq -> fz
  | Neq -> not fz
  | Gt -> (fs = fo) && not fz
  | Ge -> fs = fo
  | Lt -> fs <> fo
  | Le -> (fs <> fo) || fz

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if addr >= mem_bot && (Int64.add addr 8L) <= mem_top then
    Some (Int64.to_int (Int64.sub addr mem_bot))
  else None


(*------------------------------------------------*)
(* Here starts Jiacheng's code of helper function *)
(*------------------------------------------------*)


(* Set Condition flags *)

let set_flag_fo (m:mach) (res:Int64_overflow.t) : unit =
  m.flags.fo <- res.Int64_overflow.overflow

let set_flag_fs (m:mach) (res:int64) : unit =
  m.flags.fs <- (Int64.shift_right_logical res 63) = Int64.one

let set_flag_fz (m:mach) (res:int64) : unit =
  m.flags.fz <- res = Int64.zero

let fetch_data (m:mach) (offset:int64) : int64 =
  let addr =
    match map_addr offset with
    | Some x -> x
    | None -> raise X86lite_segfault
  in
  let data =
    int64_of_sbytes
      [ m.mem.(addr + 0); m.mem.(addr + 1); 
        m.mem.(addr + 2); m.mem.(addr + 3); 
        m.mem.(addr + 4); m.mem.(addr + 5);
        m.mem.(addr + 6); m.mem.(addr + 7) ]
  in data

let memaddr_operand (m:mach) (oper:operand) : int64 =
  match oper with
  | Ind1 imm -> 
    (match imm with
    | Lit lit -> lit
    | Lbl lbl -> failwith "unresolved label")             
  | Ind2 reg -> m.regs.(rind reg)
  | Ind3 (imm, reg) -> 
    (match imm with
    | Lit lit -> Int64.add m.regs.(rind reg) lit
    | Lbl lbl -> failwith "unresolved label")
  | _  -> failwith "direct operand"

let interp_operand (m:mach) (oper:operand) : int64 =
  match oper with
  | Imm imm  -> 
    (match imm with
    | Lit lit -> lit
    | Lbl lbl -> failwith "unresolved label")
  | Reg reg -> m.regs.(rind reg)
  | _ -> fetch_data m (memaddr_operand m oper)

let interp_amt (m:mach) (oper:operand) : int64 =
  match oper with
  | Imm imm  -> 
    (match imm with
    | Lit lit -> lit
    | Lbl lbl -> failwith "unresolved label")
  | Reg rcx -> m.regs.(rind rcx)
  | _ -> failwith "invalid amt"

let store_data (m:mach) (data:int64) (offset:int64) : unit =
  let addr = 
    (match map_addr offset with
    | Some x -> x
    | None -> raise X86lite_segfault) in
  let slist : sbyte list = sbytes_of_int64 data in
    m.mem.(addr + 0) <- List.nth slist 0;
    m.mem.(addr + 1) <- List.nth slist 1;
    m.mem.(addr + 2) <- List.nth slist 2;
    m.mem.(addr + 3) <- List.nth slist 3;
    m.mem.(addr + 4) <- List.nth slist 4;
    m.mem.(addr + 5) <- List.nth slist 5;
    m.mem.(addr + 6) <- List.nth slist 6;
    m.mem.(addr + 7) <- List.nth slist 7

let store_result (m:mach) (oper:operand) (res:int64) : unit =
  match oper with
  | Imm imm -> failwith "invalid location"
  | Reg reg -> m.regs.(rind reg) <- res
  | _ -> store_data m res (memaddr_operand m oper)

let store_byte (m:mach) (data:int64) (offset:int64) : unit =
  let addr = 
    (match map_addr offset with
    | Some x -> x
    | None -> raise X86lite_segfault) in
  let slist : sbyte list = sbytes_of_int64 data in
    m.mem.(addr) <- List.nth slist 0

let store_setbb (m:mach) (oper:operand) (res:int64) : unit =
  match oper with
  | Imm imm -> failwith "invalid location"
  | Reg reg ->   
    let clear_lower_byte = 
      Int64.logand m.regs.(rind reg) 0xFFFFFFFFFFFFFF00L in
    let lower_byte_of_res = Int64.logand res 0xFFL in
    let result = Int64.logor clear_lower_byte lower_byte_of_res in
      m.regs.(rind reg) <- result
  | _ -> store_byte m res (memaddr_operand m oper)
  
let fetch_instr (m:mach) : ins =
  let rip = m.regs.(rind Rip) in
  let instr_addr = map_addr rip in
  match instr_addr with
  | Some byte -> 
    (match m.mem.(byte) with
    | InsB0 instr -> instr
    | InsFrag -> failwith ("InsFrag at address " ^ (string_of_int byte))
    | Byte _ -> failwith ("Byte at address " ^ (string_of_int byte))
    )
  | None -> raise X86lite_segfault

(* Arithmetic Instructions *)

let negq (m:mach) (ol:operand list) : unit =
  let dest = List.nth ol 0 in
  let dest_val = interp_operand m dest in
  let res = Int64_overflow.neg dest_val in
    store_result m dest res.Int64_overflow.value;
    set_flag_fo m res;
    set_flag_fs m res.value;
    set_flag_fz m res.value;
    if dest_val = Int64.min_int then m.flags.fo <- true

let addq (m:mach) (ol:operand list) : unit =
  let src = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let src_val = interp_operand m src in
  let dest_val = interp_operand m dest in
  let res = Int64_overflow.add dest_val src_val in
    store_result m dest res.Int64_overflow.value;
    set_flag_fo m res;
    set_flag_fs m res.value;
    set_flag_fz m res.value

let subq (m:mach) (ol:operand list) : unit =
  let src = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let src_val = interp_operand m src in
  let dest_val = interp_operand m dest in
  let res = Int64_overflow.sub dest_val src_val in
    store_result m dest res.Int64_overflow.value;
    set_flag_fo m res;
    set_flag_fs m res.value;
    set_flag_fz m res.value

let imulq (m:mach) (ol:operand list) : unit =
  let src = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let src_val = interp_operand m src in
  let dest_val = interp_operand m dest in
  let res = Int64_overflow.mul dest_val src_val in
    store_result m dest res.Int64_overflow.value;
    set_flag_fo m res;
    set_flag_fs m res.value;
    set_flag_fz m res.value

let incq (m:mach) (ol:operand list) : unit =
  let dest = List.nth ol 0 in
  let dest_val = interp_operand m dest in
  let res = Int64_overflow.succ dest_val in
    store_result m dest res.Int64_overflow.value;
    set_flag_fo m res;
    set_flag_fs m res.value;
    set_flag_fz m res.value

let decq (m:mach) (ol:operand list) : unit =
  let dest = List.nth ol 0 in
  let dest_val = interp_operand m dest in
  let res = Int64_overflow.pred dest_val in
    store_result m dest res.Int64_overflow.value;
    set_flag_fo m res;
    set_flag_fs m res.value;
    set_flag_fz m res.value

(* Logic Instructions *)

let notq (m:mach) (ol:operand list) : unit =
  let dest = List.nth ol 0 in
  let dest_val = interp_operand m dest in
  let res = Int64.lognot dest_val in
    store_result m dest res

let andq (m:mach) (ol:operand list) : unit =
  let src = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let src_val = interp_operand m src in
  let dest_val = interp_operand m dest in
  let res = Int64.logand dest_val src_val in
    store_result m dest res;
    set_flag_fs m res;
    set_flag_fz m res;
    m.flags.fo <- false

let orq (m:mach) (ol:operand list) : unit =
  let src = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let src_val = interp_operand m src in
  let dest_val = interp_operand m dest in
  let res = Int64.logor dest_val src_val in
    store_result m dest res;
    set_flag_fs m res;
    set_flag_fz m res;
    m.flags.fo <- false

let xorq (m:mach) (ol:operand list) : unit =
  let src = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let src_val = interp_operand m src in
  let dest_val = interp_operand m dest in
  let res = Int64.logxor dest_val src_val in
    store_result m dest res;
    set_flag_fs m res;
    set_flag_fz m res;
    m.flags.fo <- false

(* Bit-manipulation Instructions *)

let sarq (m:mach) (ol:operand list) : unit =
  let amt = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let amt_val = interp_amt m amt in
  let dest_val = interp_operand m dest in
  let res = Int64.shift_right dest_val (Int64.to_int amt_val) in
    store_result m dest res;
    if (Int64.to_int amt_val) <> 0 then (set_flag_fs m res; set_flag_fz m res);
    if (Int64.to_int amt_val) = 1 then m.flags.fo <- false

let shlq (m:mach) (ol:operand list) : unit =
  let amt = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let amt_val = Int64.to_int (interp_amt m amt) in
  let dest_val = interp_operand m dest in
  let res = Int64.shift_left dest_val amt_val in
    store_result m dest res;
    if amt_val <> 0 then (set_flag_fs m res; set_flag_fz m res);
    if amt_val = 1 then
      let first_top_bit = Int64.shift_right_logical dest_val 63 in
      let second_top_bit = 
        Int64.logand (Int64.shift_right_logical dest_val 62) 1L in
      if (first_top_bit <> second_top_bit) then m.flags.fo <- true
      else m.flags.fo <- false

let shrq (m:mach) (ol:operand list) : unit =
  let amt = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let amt_val = interp_amt m amt in
  let dest_val = interp_operand m dest in
  let res = Int64.shift_right_logical dest_val (Int64.to_int amt_val) in
    store_result m dest res;
    if (Int64.to_int amt_val) <> 0 then
      if (Int64.to_int res = 0) then (set_flag_fs m res; set_flag_fz m res);
      if (Int64.to_int amt_val) = 1 then
        m.flags.fo <- Int64.shift_right_logical dest_val 63 = Int64.one

let setb (m:mach) (ol:operand list) (cc:cnd): unit = 
  if interp_cnd {fo = m.flags.fo; fs = m.flags.fs ; fz = m.flags.fz} cc
  then store_setbb m (List.nth ol 0) Int64.one
  else store_setbb m (List.nth ol 0) Int64.zero

(* Data-movement Instructions *)

let leaq (m:mach) (ol:operand list) : unit =
  let ind = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let ind_addr = memaddr_operand m ind in
    store_result m dest ind_addr

let movq (m:mach) (ol:operand list) : unit =
  let src = List.nth ol 0 in
  let dest = List.nth ol 1 in
  let src_val = interp_operand m src in
    store_result m dest src_val

let pushq (m:mach) (ol:operand list) : unit =
  let src = List.nth ol 0 in
  let src_val = interp_operand m src in
    m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L;
    store_result m (Ind2 Rsp) src_val

let popq (m:mach) (ol:operand list) : unit =
  let dest = List.nth ol 0 in
  let rsp_val = interp_operand m (Ind2 Rsp) in
    store_result m dest rsp_val;
    m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L

(* Control-flow and condition Instructions *)

let cmpq (m:mach) (ol:operand list) : unit =
  let src1 = List.nth ol 0 in
  let src2 = List.nth ol 1 in
  let src1_val = interp_operand m src1 in
  let src2_val = interp_operand m src2 in
  let res = Int64_overflow.sub src2_val src1_val in
  set_flag_fo m res;
  set_flag_fs m res.value;
  set_flag_fz m res.value

let jmp (m:mach) (ol:operand list) : unit =
  let src = List.nth ol 0 in
  let src_val = interp_operand m src in
    store_result m (Reg Rip) src_val

let callq (m:mach) (ol:operand list) : unit =
  let src = List.nth ol 0 in
  let src_val = interp_operand m src in
  let rip_val = interp_operand m (Reg Rip) in
    m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L;
    store_result m (Ind2 Rsp) rip_val;
    store_result m (Reg Rip) src_val

let retq (m:mach) (ol:operand list) : unit =
  let rsp_val = interp_operand m (Ind2 Rsp) in
    store_result m (Reg Rip) rsp_val;
    m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L

let j (m:mach) (ol:operand list) (cc:cnd) : unit =
  let src = List.nth ol 0 in
  let src_val = interp_operand m src in
  if interp_cnd {fo = m.flags.fo; fs = m.flags.fs ; fz = m.flags.fz} cc then
    m.regs.(rind Rip) <- src_val

let compute_ops (m:mach) (instr:ins) : unit =
  match instr with
  | (op, ol) ->
    (match op with
    | Negq -> negq m ol
    | Addq -> addq m ol
    | Subq -> subq m ol
    | Imulq -> imulq m ol
    | Incq -> incq m ol
    | Decq -> decq m ol
    | Notq -> notq m ol
    | Andq -> andq m ol
    | Orq -> orq m ol
    | Xorq -> xorq m ol
    | Sarq -> sarq m ol
    | Shlq -> shlq m ol
    | Shrq -> shrq m ol
    | Set cc -> setb m ol cc
    | Leaq -> leaq m ol
    | Movq -> movq m ol
    | Pushq -> pushq m ol
    | Popq -> popq m ol
    | Cmpq -> cmpq m ol
    | Jmp -> jmp m ol
    | Callq -> callq m ol
    | Retq -> retq m ol
    | J cc -> j m ol cc
    )


(*----------------------------------------------*)
(* Here ends Jiacheng's code of helper function *)
(*----------------------------------------------*)


(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step (m:mach) : unit =
  let instr = fetch_instr m in
    m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L;
    compute_ops m instr

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 =
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)


(*----------------------------------------------*)
(* Here starts Haoran's code of helper function *)
(*----------------------------------------------*)


module StringMap = Map.Make(String)
let generate_map(p:prog) : int64 StringMap.t =
  let result = StringMap.empty in
  let rec loop (p:prog) (result:int64 StringMap.t)
   (text_size:int64): int64 StringMap.t =
    match p with
    | [] -> result
    | {lbl; global; asm} :: t ->
      let new_text_size = match asm with
      | Text i -> Int64.add text_size (Int64.mul 8L 
                  (Int64.of_int(List.length i)))
      | _ -> text_size in
      let new_result = StringMap.add lbl 
                        (Int64.add text_size 0x400000L) result in
      loop t new_result new_text_size
    in 
    loop p result 0L
    
  
let replace_lbl_in_ins(i: ins) (l: lbl) (lbl_map: int64 StringMap.t) : ins =
  let replace_lbl_in_arg a = match a with
    | Imm (Lbl l) -> Imm (Lit ((StringMap.find l lbl_map)))
    | Ind1 (Lbl l) -> Ind1 (Lit ((StringMap.find l lbl_map)))
    | Ind3 (Lbl l, i) -> Ind3 (Lit ((StringMap.find l lbl_map)), i)
    | _ -> a
  in
  let (op, args) = i in
  (op, List.map replace_lbl_in_arg args)

let replace_lbl_in_data(d: data)(l:lbl)(lbl_map: int64 StringMap.t) : data =
  match d with
  | Quad (Lbl l) -> Quad (Lit ((StringMap.find l lbl_map)))
  | _ -> d

let replace_lbl_in_asm(a: asm)(l:lbl)(lbl_map: int64 StringMap.t) : asm =
  match a with
  | Text i -> Text (List.map (fun i -> replace_lbl_in_ins i l lbl_map) i)
  | Data d -> Data (List.map (fun d -> replace_lbl_in_data d l lbl_map) d)

(* Here are helper functions for label resolving *)

let length_of_ins : quad = 8L
let length_of_data = function
  | Asciz s -> Int64.add (Int64.of_int (String.length s)) 1L  
    (* length of string plus null terminator *)
  | Quad _ -> 8L  (* size of a quad, as int64 *)

(* Compute the length of an asm *)
let length_of_Text = function
  | Text ins_list -> List.fold_left (fun acc ins -> 
                       Int64.add acc length_of_ins) 0L ins_list
  | _ -> 0L

let length_of_Data = function
| Data data_list -> List.fold_left (fun acc data -> 
                      Int64.add acc (length_of_data data)) 0L data_list
| _ -> 0L

let rec sbytes_of_sam asm = match asm with
  | Text ins_list -> List.fold_left (fun acc ins -> 
                       acc @ sbytes_of_ins ins) [] ins_list
  | Data data_list -> List.fold_left (fun acc data -> 
                        acc @ sbytes_of_data data) [] data_list

let rec check_ins (i:ins)(map: int64 StringMap.t) : bool = 
  match i with
  | (op, args) -> List.fold_left (fun acc arg -> match arg with
    | Imm (Lbl l) -> acc && StringMap.mem l map
    | Ind1 (Lbl l) -> acc && StringMap.mem l map
    | Ind3 (Lbl l, i) -> acc && StringMap.mem l map
    | _ -> acc) true args

let rec check_data(d:data)(map: int64 StringMap.t) : bool = 
  match d with
  | Quad (Lbl l) -> StringMap.mem l map
  | _ -> true

let check_asm (a:asm)(map: int64 StringMap.t) : bool = match a with
  | Text ins_list -> List.fold_left (fun acc ins -> 
                       acc && check_ins ins map) true ins_list
  | Data data_list -> List.fold_left (fun acc data -> 
                        acc && check_data data map) true data_list


(*--------------------------------------------*)
(* Here ends Haoran's code of helper function *)
(*--------------------------------------------*)


let assemble (p:prog) : exec =
  let map = generate_map (p:prog) in
  let entry_pos = 0 in
  let res = { entry = 0L; text_pos = 0X400000L;
              data_pos = 0L; text_seg = []; data_seg = [] } in
  let rec loop (res:exec) (text_size:quad) (data_size:quad) (p:prog) : exec =
    match p with
    | [] -> if StringMap.mem "main" map then 
              {res with data_pos = Int64.add res.text_pos text_size} 
            else raise (Undefined_sym "main")
    | {lbl; global; asm}::t ->
      match asm with
      | Text i -> 
        if not(check_asm(asm) map) then raise (Undefined_sym lbl)
        else 
          let text_size = Int64.add (length_of_Text(asm)) text_size in
          let new_asm = replace_lbl_in_asm(asm) lbl map in
          let res = {res with text_seg = 
                     res.text_seg @ sbytes_of_sam(new_asm)} in
          let res = if lbl = "main" then 
                    {res with entry = Int64.add text_size 
                        (Int64.sub mem_bot (length_of_Text(asm)))}
                    else res in
          loop (res) (text_size) (data_size) (t)
      | Data d -> 
        if not(check_asm(asm) map) then raise (Undefined_sym lbl) 
        else
          let data_size = Int64.add (length_of_Data(asm)) data_size in
          let new_asm = replace_lbl_in_asm(asm) lbl map in
          let res = {res with data_seg = 
                     res.data_seg @ sbytes_of_sam(new_asm)} in
          loop (res) (text_size) (data_size) (t)
          in
      loop res 0L 0L p

(* Convert an executable into a sequence of bytes *)

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach =
  let mem = Array.make mem_size (Byte '\x00') in
  let () = List.iteri (fun i b ->
    mem.(Int64.to_int mem_top - Int64.to_int mem_bot - 8 + i) <- b)
    (sbytes_of_int64(exit_addr)) in
  let () = List.iteri (fun i b -> mem.(i) <- b) text_seg in
  let ins_num_in_sbyte = List.length text_seg in
  let data_num_in_sbyte = List.length data_seg in
  let () = List.iteri (fun i b -> mem.(i + ins_num_in_sbyte) <- b) data_seg in
  let regs = Array.make nregs 0L in
  let () = regs.(rind Rip) <- entry in
  let () = regs.(rind Rsp) <- Int64.sub mem_top 8L in

  let flag = {fo = false; fs = false; fz = false} in
  let result = {flags = flag; regs = regs; mem = mem} in
  result
