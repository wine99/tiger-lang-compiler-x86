(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

type symbol = string * int 

module H = Hashtbl

let initHtSize = 1024
let hashTable: (string, int) H.t = H.create initHtSize

let nextsym = ref 0

let symbol name =
  match H.find_opt hashTable name with
  | Some i -> (name, i)
  | None ->
    let i = !nextsym in
    nextsym := i + 1;
    H.add hashTable name i ;
    (name, i)
    
let name (s, _) = s

module ST =
  Map.Make ( struct 
    type t = symbol
    let compare (_,n1) (_,n2) = compare n1 n2
  end )
    
type 'a table = 'a ST.t

let empty = ST.empty
let enter (t, k, v) = ST.add k v t
let look (t, k ) = ST.find_opt k t
let numItems = ST.cardinal

