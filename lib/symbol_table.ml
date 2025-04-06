exception DuplicateEntry of Ast.identifier
exception NotFound of Ast.identifier

type 'a t = Empty | Node of 'a t * (Ast.identifier, 'a) Hashtbl.t
let empty_table = Empty

let begin_block sym_tab = Node(sym_tab, Hashtbl.create 0)

let end_block sym_tab = match sym_tab with
  | Empty -> Empty
  | Node(parent, _) -> parent

let add_entry identifier info sym_tab = match sym_tab with
  | Empty -> failwith "Error! Adding a symbol in an empty scope"
  | Node(parent, table) -> (
      match Hashtbl.find_opt table identifier with
        | Some _ -> raise(DuplicateEntry(identifier))
        | None -> (Hashtbl.add table identifier info); Node(parent, table)
    )

let rec lookup identifier sym_tab = match sym_tab with
  | Empty -> raise(NotFound(identifier))
  | Node(parent, table) -> (
    match Hashtbl.find_opt table identifier with
      | None -> lookup identifier parent
      | Some info -> info
    )

let of_alist lst = 
  let rec fun_aux sym_tab l = match l with
    | [] -> sym_tab
    | (identifier, info)::tail -> fun_aux (add_entry identifier info sym_tab) tail
  in (fun_aux (Node(Empty, Hashtbl.create 0)) lst)