(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)

(* ll ir compilation -------------------------------------------------------- *)

open Tigercommon
module S = Symbol
open X86
open Ll
open X86.Asm

exception BackendFatal (* use this for impossible cases *)

exception NotImplemented

(*let todo1 _ = raise NotImplemented*)

(*let todo2 _ _ = raise NotImplemented*)

let todo3 _ _ _ = raise NotImplemented

(* Helpers ------------------------------------------------------------------ *)

(* Platform-specific symbol generation *)

type os = Linux | Darwin

let os =
  let ic = Unix.open_process_in "uname" in
  let uname = input_line ic in
  let () = close_in ic in
  match uname with
  | "Linux" -> Linux
  | "Darwin" -> Darwin
  | _ -> raise BackendFatal

let mangle s =
  match os with Linux -> Symbol.name s | Darwin -> "_" ^ Symbol.name s

(* Mapping ll comparison operations to X86 condition codes *)
let compile_cnd (c : Ll.cnd) : X86.cnd =
  match c with
  | Ll.Eq -> Eq
  | Ll.Ne -> Neq
  | Ll.Slt -> Lt
  | Ll.Sle -> Le
  | Ll.Sgt -> Gt
  | Ll.Sge -> Ge

let foreach f l =
  let rec loop = function [] -> () | x :: xs -> f x ; loop xs in
  loop l

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

type layout = (Ll.uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = {tdecls: (Ll.tid * Ll.ty) list; layout: layout}

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m

(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip) %rax

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)

let compile_operand (ctxt : ctxt) (dest : X86.operand) (oper : Ll.operand) :
    ins =
  match oper with
  | Null ->
      let num = Imm (Lit 0) in
      (Movq, [num; dest])
  | Const i ->
      let num = Imm (Lit i) in
      (Movq, [num; dest])
  | Gid gid ->
      let lbl = mangle gid in
      (Leaq, [Ind3 (Lbl lbl, Rip); dest])
  | Id uid ->
      let src = List.assoc uid ctxt.layout in
      (Movq, [src; dest])

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

(* TODO :
   - Save caller-save registers before calling.
   - Restoring after return. *)
let compile_call (ctxt : ctxt) (func : Ll.operand)
    (args : (ty * Ll.operand) list) : ins list =
  (* Save registers on stack *)
  let caller_saved = [Rax; R11] in (* Add stuff later *)
  let mov_in = caller_saved |> List.map (fun x -> (Pushq, [~%x]) ) in
  (* Function call *)
  let args_86 = args |> List.map (fun x -> compile_operand ctxt ~%Rax (snd x)) in
  let func_86 = compile_operand ctxt ~%R10 func in (* maybe another reg ??? *)
  let call = (Callq, [~%R10]) in
  (* Restore registers from stack. *)
  let mov_out = caller_saved |> List.rev |> List.map (fun x -> (Popq, [~%x])) in
  mov_out @ mov_in @ args_86 @ [func_86; call]

(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelmentptr, you must generate x86 code that performs
   the appropriate arithemetic calculations.
*)

(* Function size_ty maps an LLVMlite type to a size in bytes.
   (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite
     your function should simply return 0
*)

let actual_type tdecls = function
  | ty ->
      let rec act_tpe = function
        | I1 -> I1
        | I8 -> I8
        | I64 -> I64
        | Void -> Void
        | Ptr t -> Ptr (act_tpe t)
        | Struct ts -> Struct (List.map act_tpe ts)
        | Array (n, t) -> Array (n, act_tpe t)
        | Fun (params, ret_ty) ->
            Fun (params |> List.map act_tpe, act_tpe ret_ty)
        | Namedt tid -> act_tpe @@ List.assoc tid tdecls
      in
      act_tpe ty

let rec size_ty tdecls = function
  | ty -> (
    match actual_type tdecls ty with
    | I8 | Void | Fun _ -> 0
    | I1 | I64 | Ptr _ -> 8
    | Struct ts -> ts |> List.map (size_ty tdecls) |> List.fold_left ( + ) 8
    | Array (n, t) -> n * size_ty tdecls t
    | Namedt _ -> raise BackendFatal )

let compile_gep : ctxt -> ty * Ll.operand -> Ll.operand list -> ins list =
  todo3

(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Set instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)

let compile_insn (ctxt : ctxt) ((id, ins) : uid option * insn) : ins list =
  match ins with
  | Binop (op, _, left, right) ->
      let op_x86 =
        match op with
        | Add -> Addq
        | Sub -> Subq
        | Mul -> Imulq
        | SDiv -> Idivq
        | Shl -> Shlq
        | Lshr -> Shrq
        | Ashr -> Sarq
        | And -> Andq
        | Or -> Orq
        | Xor -> Xorq
      in
      let left_x86 = compile_operand ctxt ~%R11 left in
      let right_x86 = compile_operand ctxt ~%Rax right in
      [left_x86; right_x86; (op_x86, [~%R11; ~%Rax])]
  | Alloca ty ->
      let type_width = size_ty ctxt.tdecls ty in
      [(Subq, [~$type_width; ~%Rsp])]
  | Load (_, op) ->
      let op_x86 = compile_operand ctxt ~%R11 op in
      let load_ins = (Movq, [Ind2 R11; ~%Rax]) in
      [op_x86; load_ins]
  | Store (_, src, dest) ->
      let src_x86 = compile_operand ctxt ~%R11 src in
      let dest_x86 = compile_operand ctxt ~%Rax dest in
      let store_ins = (Movq, [Ind2 R11; Ind2 Rax]) in
      [src_x86; dest_x86; store_ins]
  | Icmp (cnd, _, left, right) ->
      let cndx86 : X86.cnd =
        match cnd with
        | Eq -> Eq
        | Ne -> Neq
        | Slt -> Lt
        | Sle -> Le
        | Sgt -> Gt
        | Sge -> Ge
      in
      let left_x86 = compile_operand ctxt ~%R11 left in
      let right_x86 = compile_operand ctxt ~%Rax right in
      let cmp = (Cmpq, [~%R11; ~%Rax]) in
      let set = (Set cndx86, []) in
      [left_x86; right_x86; cmp; set]
  | Call (ty, func, args) -> compile_call ctxt func args
  | Bitcast (_, op, _) -> [compile_operand ctxt ~%Rax op]
  | Gep (ty, operand, ls) -> compile_gep ctxt (ty, operand) ls
  | Zext (_, op, _) -> [compile_operand ctxt ~%Rax op]
  | Ptrtoint (_, op, _) -> [compile_operand ctxt ~%Rax op]
  | Comment str -> raise NotImplemented

(* compiling terminators  --------------------------------------------------- *)

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional
*)

let compile_terminator (ctxt : ctxt) (term : terminator) : ins list =
  match term with
  | Ret (_, oper_opt) -> (
      let reset_sp = (Movq, [~%Rbp; ~%Rsp]) in
      let pop_frame = (Popq, [~%Rbp]) in
      let ret = (Retq, []) in
      let reset = [reset_sp; pop_frame; ret] in
      match oper_opt with
      | None -> reset
      | Some oper -> compile_operand ctxt ~%Rax oper :: reset )
  | Br uid ->
      let lbl = ctxt.layout |> List.assoc uid in
      [(Jmp, [lbl])]
  | Cbr (oper, uid1, uid2) ->
      let lbl1 = ctxt.layout |> List.assoc uid1 in
      let lbl2 = ctxt.layout |> List.assoc uid2 in
      let op_86 = compile_operand ctxt ~%Rax oper in
      let cmp = (Cmpq, [~%Rax; Imm (Lit 0)]) in
      let jmp1 = (J Eq, [lbl2]) in
      let jmp2 = (Jmp, [lbl1]) in
      [op_86; cmp; jmp1; jmp2]

(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. *)
let compile_block (ctxt : ctxt) ({insns; terminator} : block) : ins list =
  let f acc x = acc @ compile_insn ctxt x in
  let insns_86 : ins list = insns |> List.fold_left f [] in
  let term_86 = compile_terminator ctxt terminator in
  insns_86 @ term_86

let compile_lbl_block (lbl : lbl) (ctxt : ctxt) (block : block) : elem =
  let lbl_str = mangle lbl in
  let global = false in
  (* Not sure about this... *)
  let block_86 = compile_block ctxt block in
  let asm = Text block_86 in
  {lbl= lbl_str; global; asm}

(* compile_fdecl ------------------------------------------------------------ *)

(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)

let arg_loc : int -> X86.operand = function
  | 0 -> ~%Rdi
  | 1 -> ~%Rsi
  | 2 -> ~%Rdx
  | 3 -> ~%Rcx
  | 4 -> ~%R08
  | 5 -> ~%R09
  | n ->
      let r = (n - 6) * 8 in
      Ind3 (Lit r, Rbp)

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

let lbl_of = function uid -> S.name uid

let rec drop n = function
  | [] -> []
  | _ :: xs when n > 0 -> drop (n - 1) xs
  | ls -> ls

let enumerate l =
  let rec loop n acc = function
    | [] -> acc
    | _ :: xs -> loop (n + 1) (acc @ [n]) xs
  in
  loop 0 [] l

(* what to do about stack space for local declarations? i.e. what about the layout??? *)
let compile_fdecl (tdecls : (uid * ty) list) (uid : uid)
    ({fty= arg_ty, ret_ty; param; cfg} : fdecl) : elem list =
  let old_ptr = (Pushq, [~%Rbp]) in
  let new_ptr = (Movq, [~%Rsp; ~%Rbp]) in
  let stack_args = arg_ty |> drop 6 in
  let args_size =
    stack_args |> List.map (size_ty tdecls) |> List.fold_left ( + ) 0
  in
  let locals_size =
    raise NotImplemented
    (* locals_size should not map over tdecls but rather some list of local var declarations *)
    (*tdecls |> List.map snd |> List.map (size_ty tdecls) |> List.fold_left ( + ) 0*)
  in
  let local_space = (Subq, [~$(args_size + locals_size); ~%Rsp]) in
  let prologue : ins list = [old_ptr; new_ptr; local_space] in
  let arg_locs = param |> enumerate |> List.map arg_loc in
  let arg_layout = List.combine param arg_locs in
  let layout = arg_layout in
  let ctxt = {tdecls; layout} in
  let entry_block =
    gtext (lbl_of uid) (prologue @ compile_block ctxt (fst cfg))
  in
  let f_lbl_block x acc = compile_lbl_block (fst x) ctxt (snd x) :: acc in
  let lbl_blocks : elem list = List.fold_right f_lbl_block (snd cfg) [] in
  entry_block :: lbl_blocks

(* compile_gdecl ------------------------------------------------------------ *)

(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)

let rec compile_ginit = function
  | GNull -> [Quad (Lit 0)]
  | GGid gid -> [Quad (Lbl (mangle gid))]
  | GInt c -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs -> List.concat (List.map compile_gdecl gs)
  | GStruct gs -> List.concat (List.map compile_gdecl gs)

and compile_gdecl (_, g) = compile_ginit g

(* compile_prog ------------------------------------------------------------- *)

let compile_prog ({tdecls; gdecls; fdecls} : Ll.prog) : X86.prog =
  let g (lbl, gdecl) = Asm.data (mangle lbl) (compile_gdecl gdecl) in
  let f (name, fdecl) = compile_fdecl tdecls name fdecl in
  List.map g gdecls @ List.concat (List.map f fdecls)
