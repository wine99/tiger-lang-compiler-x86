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

let split_index i l =
  let rec loop j acc = function
    | [] -> (List.rev acc, [])
    | x :: xs ->
        if j > 0 then loop (j - 1) (x :: acc) xs else (List.rev acc, xs)
  in
  loop i [] l

let lbl_of = function uid -> S.name uid

let enumerate = List.mapi (fun i _ -> i)

let is_even = function n -> n mod 2 = 0

let align = function n when n mod 16 = 0 -> n | n -> n + 8

(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)

let arg_loc (arg_n : int) : X86.operand =
  match arg_n with
  | 0 -> ~%Rdi
  | 1 -> ~%Rsi
  | 2 -> ~%Rdx
  | 3 -> ~%Rcx
  | 4 -> ~%R08
  | 5 -> ~%R09
  | n ->
      let r = (n - 4) * 8 in
      Ind3 (Lit r, Rbp)

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
(*
    - save caller-save registers on stack before calling (done)
    - push args to registers and stack
    - call func (?done)
    - pop args from stack (i.e. add to rsp) 
    - restore caller-save registers (done)
    - maybe take additional arg from compile_inst that specifies destination
    (i.e. if %rax is supposed to go to a stack slot) - match on this in compile_instn -- not here
      *)
let compile_call (ctxt : ctxt) (target : X86.operand option)
    (func : Ll.operand) (args : (ty * Ll.operand) list) : ins list =
  let caller_saved = [Rax; R11; Rcx; Rdx; Rsi; Rdi; R08; R09; R10] in
  let mov_in = caller_saved |> List.map (fun x -> (Pushq, [~%x])) in
  (* Function call *)
  let arg_reg, arg_stack = split_index 6 args in
  let mov_arg_reg =
    arg_reg |> List.mapi (fun i (_, x) -> compile_operand ctxt (arg_loc i) x)
  in
  let f_mov_arg_stack (_, x) =
    compile_operand ctxt ~%Rax x :: [(Pushq, [~%Rax])]
  in
  let mov_arg_stack =
    arg_stack |> List.rev |> List.concat_map f_mov_arg_stack
  in
  let mov_arg_stack =
    if is_even (List.length arg_stack) then mov_arg_stack
    else (Subq, [~$8; ~%Rsp]) :: mov_arg_stack
  in
  let func_86 = compile_operand ctxt ~%R10 func in
  let call = (Callq, [~%R10]) in
  let store_result =
    match target with Some target -> [(Movq, [~%Rax; target])] | None -> []
  in
  let undo_mov_arg_stack =
    (Addq, [~$(List.length arg_stack |> ( * ) 8 |> align); ~%Rsp])
  in
  (* Restore registers from stack. *)
  let mov_out =
    caller_saved |> List.rev |> List.map (fun x -> (Popq, [~%x]))
  in
  mov_in @ mov_arg_reg @ mov_arg_stack @ [func_86; call] @ store_result
  @ [undo_mov_arg_stack] @ mov_out

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
        | Ptr t -> Ptr t
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
    | Struct ts -> ts |> List.map (size_ty tdecls) |> List.fold_left ( + ) 0
    | Array (n, t) -> n * size_ty tdecls t
    | Namedt _ -> raise BackendFatal )

(* gep my_rec* %my_rec0, i32 i, i32 j *)
(* i * op_size + op_86 + 8 * j *)
let compile_gep (ctxt : ctxt) (target : X86.operand)
    ((op_ty, op) : ty * Ll.operand) (indices : Ll.operand list) : ins list =
  let ty = actual_type ctxt.tdecls op_ty in
  let op_size = size_ty ctxt.tdecls ty in
  let op_86 = compile_operand ctxt ~%Rax op in
  let offset =
    match indices with
    (* array indexing *)
    | [i] ->
        [ (Movq, [~$op_size; ~%R11])
        ; compile_operand ctxt ~%R10 i
        ; (Imulq, [~%R10; ~%R11])
        ; (Addq, [~%R11; ~%Rax]) ]
    (* field accessing *)
    | [Const 0; j] ->
        [ compile_operand ctxt ~%R11 j
        ; (Imulq, [~$8; ~%R11])
        ; (Addq, [~%R11; ~%Rax]) ]
    | _ -> raise BackendFatal
  in
  (op_86 :: offset) @ [(Movq, [~%Rax; target])]

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

let compile_insn (ctxt : ctxt) ((opt_local_var, insn) : uid option * insn) :
    ins list =
  let lookup = lookup ctxt.layout in
  let comment =
    (X86.Comment (string_of_named_insn (opt_local_var, insn)), [])
  in
  match insn with
  | Binop (op, _, left, right) -> (
      let op_x86 =
        match op with
        | Add -> Addq (* Not-ordered *)
        | Sub -> Subq (* Ordered *)
        | Mul -> Imulq (* Not-ordered *)
        | SDiv -> Idivq (* Order *)
        | Shl -> Shlq (* Order, switch order for x86 *)
        | Lshr -> Shrq (* Order, switch order for x86 *)
        | Ashr -> Sarq (* Order, switch order for x86 *)
        | And -> Andq (* Not-ordered *)
        | Or -> Orq (* Not-ordered *)
        | Xor -> Xorq (* Not-ordered *)
      in
      let left_reg = ~%Rax in
      let right_reg = ~%R11 in
      let left_x86 = compile_operand ctxt left_reg left in
      let right_x86 = compile_operand ctxt right_reg right in
      let op =
        match op_x86 with
        | Idivq ->
            [ (Pushq, [~%Rdx])
            ; (Cqto, [])
            ; (op_x86, [right_reg])
            ; (Popq, [~%Rdx]) ]
        | Subq | Shlq | Shrq | Sarq ->
            [(op_x86, [right_reg; left_reg]); (Movq, [left_reg; right_reg])]
        | _ -> [(op_x86, [left_reg; right_reg])]
      in
      match (opt_local_var, op_x86) with
      | Some id, Idivq ->
          [comment; left_x86; right_x86] @ op @ [(Movq, [~%Rax; lookup id])]
      | Some id, _ ->
          [comment; left_x86; right_x86]
          @ op
          @ [(Movq, [right_reg; lookup id])]
      | None, _ -> raise BackendFatal )
  | Alloca _ -> (
    (* x = alloc y
       y occupies some amount of memory in stack,
       and x is the pointer next to it (on the lower side),
       this also agrees with the func size_of_uid in func collect_uids *)
    match opt_local_var with
    | Some uid ->
        [ comment
        ; (Leaq, [lookup uid; ~%Rax])
        ; (Addq, [~$8; ~%Rax])
        ; (Movq, [~%Rax; lookup uid]) ]
    | _ -> raise BackendFatal )
  | Load (_, op) ->
      let op_x86 = compile_operand ctxt ~%R11 op in
      let load_ins = (Movq, [Ind2 R11; ~%Rax]) in
      let store_back =
        match opt_local_var with
        | Some id -> (Movq, [~%Rax; lookup id])
        | None -> raise BackendFatal
      in
      [comment; op_x86; load_ins; store_back]
  | Store (_, src, dest) ->
      let src_x86 = compile_operand ctxt ~%R11 src in
      let dest_x86 = compile_operand ctxt ~%Rax dest in
      let store_ins = (Movq, [~%R11; Ind2 Rax]) in
      [comment; src_x86; dest_x86; store_ins]
  | Icmp (cnd, _, left, right) -> (
      let cndx86 = compile_cnd cnd in
      let left_x86 = compile_operand ctxt ~%R11 left in
      let right_x86 = compile_operand ctxt ~%Rax right in
      (* operands of cmp in x86 are reversed *)
      let cmp = (Cmpq, [~%Rax; ~%R11]) in
      let res =
        Option.map
          (fun id ->
            let op = lookup id in
            [ comment
            ; left_x86
            ; right_x86
            ; cmp
            ; (Movq, [~$0; op])
            ; (Set cndx86, [op]) ] )
          opt_local_var
      in
      match res with Some x -> x | None -> raise BackendFatal )
  | Call (_, func, args) -> (
    match opt_local_var with
    | Some id -> comment :: compile_call ctxt (Some (lookup id)) func args
    | None -> comment :: compile_call ctxt None func args )
  | Gep (ty, operand, ls) -> (
    match opt_local_var with
    | Some id -> comment :: compile_gep ctxt (lookup id) (ty, operand) ls
    | None -> raise BackendFatal )
  | Bitcast (_, op, _) | Zext (_, op, _) | Ptrtoint (_, op, _) -> (
    match opt_local_var with
    | Some id ->
        [comment; compile_operand ctxt ~%Rax op; (Movq, [~%Rax; lookup id])]
    | None -> raise BackendFatal )
  | Comment _ -> []

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
      let restore_rbp = (Popq, [~%Rbp]) in
      let ret = (Retq, []) in
      let reset = [reset_sp; restore_rbp; ret] in
      match oper_opt with
      | None -> reset
      | Some oper -> compile_operand ctxt ~%Rax oper :: reset )
  | Br uid -> [(Jmp, [~$$(mangle uid)])]
  | Cbr (oper, uid1, uid2) ->
      let op_86 = compile_operand ctxt ~%Rax oper in
      let reg_of_0 = (Movq, [~$0; ~%R11]) in
      let cmp = (Cmpq, [~%Rax; ~%R11]) in
      let jmp1 = (J Eq, [~$$(mangle uid2)]) in
      let jmp2 = (Jmp, [~$$(mangle uid1)]) in
      [op_86; reg_of_0; cmp; jmp1; jmp2]

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

let collect_uids tdecls (cfg : cfg) =
  let size_of_uid tdecls = function
    (* see comment in the Alloca case in func compile_insn *)
    | Alloca ty -> size_ty tdecls ty + 8
    | _ -> 8
  in
  let rec loop acc = function
    | [] -> acc
    | (Some uid, insn) :: tail ->
        loop ((uid, size_of_uid tdecls insn) :: acc) tail
    | (None, _) :: tail -> loop acc tail
  in
  let ( >> ) f g x = g (f x) in
  let head_block = loop [] (fst cfg).insns |> List.rev in
  let tail_block =
    snd cfg |> List.map snd
    |> List.map (fun b -> b.insns)
    |> List.concat_map (loop [] >> List.rev)
  in
  head_block @ tail_block

(* construct layout - figure out how to get uids of local vars *)
(*
   - create x86 function prologue (done)
   - save callee-saved registers (only those we use) (we don't use any -> done)
   - construct layout (done)
   (and decrement rsp to acommodate these vars i.e. get total amount of space,
    note that args are before the return addr so we don't need to allocate space for these) (done)
   - compile body (done)
   - create x86 function epilogue (done, handled by compile_terminator)
   - ensure rsp is 16 byte aligned (just check mod 16) (done)
   *)

let compile_fdecl (tdecls : (uid * ty) list) (uid : uid)
    ({param; cfg; _} : fdecl) : elem list =
  let old_ptr = (Pushq, [~%Rbp]) in
  let new_ptr = (Movq, [~%Rsp; ~%Rbp]) in
  (* `locals` is a list of `(uid, size)` *)
  let locals = collect_uids tdecls cfg in
  let locals_size, locals_layout =
    List.fold_left_map
      (fun index (id, size) ->
        let new_index = index + size in
        (new_index, (id, Ind3 (Lit (-new_index), Rbp))) )
      0 locals
  in
  let locals_size = align locals_size in
  let local_space = (Subq, [~$locals_size; ~%Rsp]) in
  let prologue : ins list = [old_ptr; new_ptr; local_space] in
  let arg_layout =
    param |> enumerate |> List.map arg_loc |> List.combine param
  in
  let layout = arg_layout @ locals_layout in
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
