
    
(* attribution: https://gist.github.com/lindig/be55f453026c65e761f4e7012f8ab9b5 *) 
let findByExtension ?(extraMatcher=fun _ -> true) ?(sort=true) exts dir =
  let isMatch fname = 
    List.mem (Filename.extension fname) exts && (extraMatcher fname)
    in
  

  let rec loop result = function
    | f::fs when Sys.is_directory f ->
          Sys.readdir f
          |> Array.to_list
          |> List.map (Filename.concat f)
          |> List.append fs
          |> loop result
    | f::fs when isMatch f -> loop (f::result) fs
    | _::fs -> loop result fs 
    | []    -> result
  in
    (loop [] [dir]) |> if sort then List.sort compare else Fun.id