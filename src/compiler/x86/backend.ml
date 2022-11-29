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

let todo1 _ = raise NotImplemented
let todo2 _ _ = raise NotImplemented 
let todo3 _ _ _ = raise NotImplemented


(* Helpers ------------------------------------------------------------------ *)


(* Platform-specific symbol generation *)

type os = Linux | Darwin

let os =  
  let ic = Unix.open_process_in "uname" in
  let uname = input_line ic in
  let () = close_in ic in
  match uname with 
     "Linux" -> Linux 
   | "Darwin" -> Darwin 
   | _ -> raise BackendFatal

let mangle s =
    match os with 
	      Linux -> Symbol.name s
     |  Darwin -> "_" ^ (Symbol.name s)
    

(* Mapping ll comparison operations to X86 condition codes *)
let compile_cnd (c:Ll.cnd) : X86.cnd =
  match c with
    Ll.Eq  -> X86.Eq
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

type layout = (Ll.uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (Ll.tid * Ll.ty) list
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


let compile_operand: ctxt -> X86.operand -> Ll.operand -> ins = todo3


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

let size_ty: (uid * ty) list -> ty -> quad = todo2 

let compile_gep: ctxt -> ty * Ll.operand -> Ll.operand list -> ins list = todo3
     

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

let compile_insn ctxt (id, ins): ctxt -> uid option * insn -> ins list = match ins with
  | Binop (bop, ty, left_oper, right_oper) -> todo2
  | Alloca ty -> todo2
  | Load (ty, oper) -> todo2
  | Store (ty, from_oper, to_oper) -> todo2
  | Icmp (cnd, ty, left_oper, right_oper) -> todo2
  | _ -> todo2
(*| Call of ty * Ll.operand * (ty * Ll.operand) list
  | Bitcast of ty * Ll.operand * ty
  | Gep of ty * Ll.operand * Ll.operand list
  | Zext of ty * Ll.operand * ty
  | Ptrtoint of ty * Ll.operand * ty
  | Comment of lbl
   *)

(* compiling terminators  --------------------------------------------------- *)

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional
*)

let compile_terminator: ctxt -> terminator -> ins list = todo2


(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. *)
let compile_block: ctxt -> block -> ins list = todo2
  
let compile_lbl_block: lbl -> ctxt -> block -> elem = todo3


(* compile_fdecl ------------------------------------------------------------ *)

(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)

let arg_loc: int -> X86.operand = function
| 0 -> X86.Reg X86.Rdi
| 1 -> X86.Reg X86.Rsi
| 2 -> X86.Reg X86.Rdx
| 3 -> X86.Reg X86.Rcx
| 4 -> X86.Reg X86.R08
| 5 -> X86.Reg X86.R09
| n -> (
  let r = (n-5)*8 in
  X86.Ind3(X86.Lit r, X86.Rbp)
  )

  
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

let compile_fdecl : (uid * ty) list -> uid -> fdecl -> elem list = todo3
   

(* compile_gdecl ------------------------------------------------------------ *)

(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)

let rec compile_ginit = function 
    GNull -> [Quad (Lit 0)]
  | (GGid gid)   -> [Quad (Lbl (mangle gid))]
  | (GInt c)     -> [Quad (Lit c)]
  | (GString s)  -> [Asciz s]
  | (GArray gs)  -> List.concat (List.map compile_gdecl gs)
  | (GStruct gs) -> List.concat (List.map compile_gdecl gs)
and compile_gdecl (_, g) = compile_ginit g

(* compile_prog ------------------------------------------------------------- *)

let compile_prog ({tdecls; gdecls; fdecls}:Ll.prog) : X86.prog =  
  let g (lbl, gdecl) = Asm.data (mangle lbl) (compile_gdecl gdecl) in 
  let f (name, fdecl) = compile_fdecl tdecls name fdecl in 
  (List.map g gdecls) @ (List.concat (List.map f fdecls))
  

