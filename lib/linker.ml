exception LinkingError of string
let ignore () = failwith "* IGNORE *"

(* 
 This type represents the information we need to mantain during the linking phase for a component.
 The connections (ID1.ID2 -> ID3.ID4) are stored in a hash table, where the key is the name of the interface (ID2)
 that is mapped in the pair (ID3, ID4).
 *)
type comp_info = Comp_info of { uses : Ast.identifier list; provides : Ast.identifier list; connections : (Ast.identifier, (Ast.identifier * Ast.identifier)) Hashtbl.t } 

(* This function gets the connection of a component and checks if the connections are correct *)
let get_connections table components connections = 
  let rec get_connections_aux connections =
    match connections with
    | [] -> table
    | h::t ->
      match h with
      | Ast.Link(id1, id2, id3, id4) ->
        let comp_id1_uses = 
          match Hashtbl.find_opt table id1 with
          | None -> raise (LinkingError(Printf.sprintf "Component %s used in a connection \"%s.%s <- %s.%s\" is not defined" id1 id1 id2 id3 id4))
          | Some Comp_info({ uses; _}) -> uses
        in
        let comp_id3_provides = 
          match Hashtbl.find_opt table id3 with
          | None -> raise (LinkingError(Printf.sprintf "Component %s used in a connection \"%s.%s <- %s.%s\" is not defined" id1 id1 id2 id3 id4))
          | Some Comp_info({ provides; _}) -> provides
        in
          let _ = 
            if id1 = id3 then raise (LinkingError(Printf.sprintf "Connection \"%s.%s <- %s.%s\" is not valid. It has been used the same identifier for the two components" id1 id2 id3 id4))
            else if not(List.mem id2 comp_id1_uses) then raise (LinkingError(Printf.sprintf "Connection \"%s.%s <- %s.%s\" is not valid. %s is not an interface used by %s" id1 id2 id3 id4 id2 id1))
            else if not(List.mem id4 comp_id3_provides) then raise (LinkingError(Printf.sprintf "Connection \"%s.%s <- %s.%s\" is not valid. %s is not an interface provided by %s" id1 id2 id3 id4 id4 id3))
            else if id2 <> id4 then raise (LinkingError(Printf.sprintf "Connection \"%s.%s <- %s.%s\" is not valid. The two interfaces must be the same" id1 id2 id3 id4))
            else let comp_id1_connections = match Hashtbl.find_opt table id1 with | None -> ignore () | Some Comp_info({ connections; _}) -> connections in
              match Hashtbl.find_opt comp_id1_connections id2 with
              | None -> Hashtbl.add comp_id1_connections id2 (id3, id4)
              | Some (id3_, _) -> raise (LinkingError(Printf.sprintf "Connection \"%s.%s <- %s.%s\" is not valid. Interface %s is already linked with component %s" id1 id2 id3 id4 id4 id3_))
          in 
            get_connections_aux t
  in
  let rec check_connections table components = 
    match components with
    | [] -> table
    | h::t ->
      match h.Ast.node with
      | Ast.ComponentDecl({ cname; _}) -> 
        let (uses, connections_comp) = (match Hashtbl.find_opt table cname with | None -> ignore () | Some Comp_info({ uses; connections; _ }) -> (uses, connections)) in
        let rec aux connections_comp uses = 
          match uses with
          | [] -> ()
          | h::t -> 
            match Hashtbl.find_opt connections_comp h with
            | None -> raise (LinkingError(Printf.sprintf "It has not been provided a connection for interface %s in component %s" h cname))
            | Some _ -> aux connections_comp t
        in
          let _ = aux connections_comp uses in 
            check_connections table t
  in
    let table = get_connections_aux connections in
      check_connections table components

let rec check_stmt cname conn_table ast_node =
  match ast_node.Ast.node with
  | Ast.If(e, s1, s2) -> 
    let ce = check_expr cname conn_table e in
    let cs1 = check_stmt cname conn_table s1 in
    let cs2 = check_stmt cname conn_table s2 in
      Ast.make_node (Ast.If(ce, cs1, cs2)) ast_node.Ast.annot
  | Ast.While(e, s) ->
    let ce = check_expr cname conn_table e in
    let cs = check_stmt cname conn_table s in
      Ast.make_node (Ast.While(ce, cs)) ast_node.Ast.annot
  | Ast.DoWhile(e, s) ->
    let ce = check_expr cname conn_table e in
    let cs = check_stmt cname conn_table s in
      Ast.make_node (Ast.DoWhile(ce, cs)) ast_node.Ast.annot
  | Ast.For(e1, e2, e3, s) ->
    let ce1 = match e1 with | None -> None | Some e1 -> Some (check_expr cname conn_table e1) in
    let ce2 = match e2 with | None -> None | Some e2 -> Some (check_expr cname conn_table e2) in
    let ce3 = match e3 with | None -> None | Some e3 -> Some (check_expr cname conn_table e3) in
    let cs = check_stmt cname conn_table s in
      Ast.make_node (Ast.For(ce1, ce2, ce3, cs)) ast_node.Ast.annot
  | Ast.Expr(e) -> 
    let ce = check_expr cname conn_table e in
      Ast.make_node (Ast.Expr(ce)) ast_node.Ast.annot
  | Ast.Return(e) ->
    begin
      match e with
      | None -> Ast.make_node (Ast.Return(None)) ast_node.Ast.annot
      | Some e ->
        let ce = check_expr cname conn_table e in
          Ast.make_node (Ast.Return(Some ce)) ast_node.Ast.annot
    end
  | Ast.Block(s) ->
    let rec check_block = function
      | [] -> []
      | h::t -> (check_stmtordec cname conn_table h)::(check_block t)
    in
    let cs = check_block s in
      Ast.make_node (Ast.Block(cs)) ast_node.Ast.annot
  | Ast.Skip -> ast_node

and check_stmtordec cname conn_table ast_node =
  match ast_node.Ast.node with
  | Ast.LocalDecl(_) -> ast_node
  | Ast.Stmt(s) ->
    let cs = check_stmt cname conn_table s in
      Ast.make_node (Ast.Stmt(cs)) ast_node.Ast.annot
and check_expr cname conn_table ast_node =
  match ast_node.Ast.node with
  | Ast.LV(l) ->
    let cl = check_lvalue cname conn_table l in
      Ast.make_node (Ast.LV(cl)) ast_node.Ast.annot
  | Ast.Assign(l, e) ->
    let cl = check_lvalue cname conn_table l in
    let ce = check_expr cname conn_table e in
      Ast.make_node (Ast.Assign(cl, ce)) ast_node.Ast.annot
  | Ast.ILiteral(_) -> ast_node
  | Ast.CLiteral(_) -> ast_node
  | Ast.BLiteral(_) -> ast_node
  | Ast.UnaryOp(uop, e) ->
    let ce = check_expr cname conn_table e in
      Ast.make_node (Ast.UnaryOp(uop, ce)) ast_node.Ast.annot
  | Ast.Address(l) ->
    let cl = check_lvalue cname conn_table l in
      Ast.make_node (Ast.Address(cl)) ast_node.Ast.annot
  | Ast.BinaryOp(binop, e1, e2) ->
    let ce1 = check_expr cname conn_table e1 in
    let ce2 = check_expr cname conn_table e2 in
      Ast.make_node (Ast.BinaryOp(binop, ce1, ce2)) ast_node.Ast.annot
  | Ast.Call(None, fname, e) ->
    let rec aux = function
    | [] -> []
      | h::t -> (check_expr cname conn_table h)::(aux t)
    in
      Ast.make_node (Ast.Call(Some cname, fname, aux e)) ast_node.Ast.annot
  | Ast.Call(Some iname, fname, e) ->
    begin
      let rec aux = function
      | [] -> []
        | h::t -> (check_expr cname conn_table h)::(aux t)
      in
        if iname = "Prelude" then (Ast.make_node (Ast.Call(Some "Prelude", fname, aux e)) ast_node.Ast.annot)
        else
          match Hashtbl.find_opt conn_table iname with
          | None -> raise (LinkingError(Printf.sprintf "Interface %s unknown" iname))
          | Some (id3, _) -> (Ast.make_node (Ast.Call(Some id3, fname, aux e)) ast_node.Ast.annot)
    end
  | Ast.IncDec(l, ido) -> 
    let cl = check_lvalue cname conn_table l in
      Ast.make_node (Ast.IncDec(cl, ido)) ast_node.Ast.annot

and check_lvalue cname conn_table ast_node =
  match ast_node.Ast.node with
  | Ast.AccVar(id_opt, id) ->
    begin
    match id_opt with
    | None -> ast_node
    | Some i ->
      match Hashtbl.find_opt conn_table i with 
      | None -> ast_node
      | Some (id3, _) -> Ast.make_node (Ast.AccVar(Some id3, id)) ast_node.Ast.annot
    end
  | Ast.AccIndex(l, e) ->
    let cl = check_lvalue cname conn_table l in
    let ce = check_expr cname conn_table e in
      Ast.make_node (Ast.AccIndex(cl, ce)) ast_node.Ast.annot

let wire_components ast =
  match ast with
    | Ast.CompilationUnit({ components; connections; interfaces }) ->
      let table = Hashtbl.create 0 in
      (* This function initializes the hashtable getting the info of all the components in the program *)
      let rec get_components components = 
        match components with
        | [] -> table
        | h::t ->
          match h.Ast.node with
          | Ast.ComponentDecl({ cname; uses; provides; _ }) ->
            let _ = Hashtbl.add table cname (Comp_info({ uses = uses; provides = provides; connections = Hashtbl.create 0})) in
              get_components t
      in
        let table = get_components components in
        let table = get_connections table components connections in
        (* This function annotates the external names with the name of the component specified in the connections *)
        let rec check_components components =
          match components with
          | [] -> []
          | h::t ->
            match h.Ast.node with
            | Ast.ComponentDecl({ cname; uses; provides; definitions; }) ->
              match Hashtbl.find_opt table cname with
              | None -> ignore ()
              | Some Comp_info({ connections; _ }) ->
                let rec check_member_decl definitions =
                  match definitions with
                  | [] -> []
                  | h::t -> 
                    match h.Ast.node with
                    | Ast.VarDecl(_) -> h::(check_member_decl t)
                    | Ast.FunDecl({ Ast.body = None; _ }) -> ignore ()
                    | Ast.FunDecl({ Ast.rtype; fname; formals; body = Some s }) ->
                      let cs = check_stmt cname connections s in
                        (Ast.make_node (Ast.FunDecl({ Ast.rtype = rtype; fname = fname; formals = formals; body = Some cs })) h.Ast.annot)::(check_member_decl t)
                in
                  (Ast.make_node (Ast.ComponentDecl({ cname = cname; uses = uses; provides = provides; definitions = check_member_decl definitions; })) h.Ast.annot)::(check_components t)
        in
        Ast.CompilationUnit({ components = check_components components;  connections = connections; interfaces = interfaces })
