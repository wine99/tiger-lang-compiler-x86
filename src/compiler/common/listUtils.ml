exception ListEmpty
let rec take n ls =  (* obs; non-tail recursive *)
  match n, ls 
      with 0, _ -> []
         | _, x::xs -> x :: take (n-1) xs 
         | _ -> raise ListEmpty 

let last xs = List.rev xs |> List.hd 

