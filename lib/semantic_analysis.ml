exception Semantic_error of Location.code_pos * string

(* Symbol elements for the symble table *)
type symbols =
  | Interface_sym of Ast.identifier * Ast.typ * symbols Symbol_table.t * Location.code_pos
    (* (component name * component type * component symbol table * uses symbol table * provides symbol table * code position) *)
  | Component_sym of Ast.identifier * Ast.typ * symbols Symbol_table.t * symbols Symbol_table.t * symbols Symbol_table.t * Location.code_pos
  | Fun_sym of Ast.identifier * Ast.typ * symbols Symbol_table.t * Location.code_pos
  | Var_sym of Ast.identifier * Ast.typ * Location.code_pos

let ignore () = failwith "* IGNORE *"

let rec is_not_scalar = function
  | Ast.TArray(_) -> true
  | Ast.TRef(typ) -> is_not_scalar typ
  | _ -> false

(* Loads the interfaces of the standard library *)
let get_mcomp_stdlib sym_tab =
  let symbols list = List.map (fun (fname, ftyp) -> (fname, Fun_sym(fname, ftyp, Symbol_table.empty_table, Location.dummy_code_pos))) list in
  let app_symbol = Interface_sym("App", Ast.TInterface("App"), Symbol_table.of_alist (symbols Mcomp_stdlib.app_signature), Location.dummy_code_pos) in
  let prelude_symbol = Interface_sym("Prelude", Ast.TInterface("Prelude"), Symbol_table.of_alist (symbols Mcomp_stdlib.prelude_signature), Location.dummy_code_pos) in
    Symbol_table.add_entry "App" app_symbol (Symbol_table.add_entry "Prelude" prelude_symbol sym_tab)

(* Initializes the global scope getting the interfaces of the program and their declarations *)
let rec get_interfaces sym_tab interfaces =
  match interfaces with
    | [] -> sym_tab
    | h::t ->
      (* Gets the declarations of an interface *)
      let rec get_declarations sym_tab declarations =
        match declarations with
        | [] -> sym_tab
        | h::t ->
          let (id, sym) =
            match h.Ast.node with
            | Ast.VarDecl(vname, typ) -> (vname, Var_sym(vname, typ, h.Ast.annot))
            | Ast.FunDecl({ Ast.rtype; Ast.fname; Ast.formals; _ }) -> 
              match rtype with
              | Ast.TInt | Ast.TBool | Ast.TChar | Ast.TVoid -> (fname, Fun_sym(fname, Ast.TFun((List.map snd formals), rtype), Symbol_table.empty_table, h.Ast.annot))
              | _ -> raise (Semantic_error(h.Ast.annot, "Functions can only returns values of type: int, bool, char, void"))
          in 
            try
              get_declarations (Symbol_table.add_entry id sym sym_tab) t
            with Symbol_table.DuplicateEntry(_) ->
              raise (Semantic_error(h.Ast.annot, (Printf.sprintf "Identifier %s was already defined in this interface" id)))
      in
        match h.Ast.node with
        | Ast.InterfaceDecl({ iname; declarations }) -> 
          try
            let sym_tab_interface = get_declarations (Symbol_table.begin_block Symbol_table.empty_table) declarations in
              get_interfaces (Symbol_table.add_entry iname (Interface_sym(iname, Ast.TInterface(iname), sym_tab_interface, h.Ast.annot)) sym_tab) t 
          with Symbol_table.DuplicateEntry(_) ->
            raise (Semantic_error(h.Ast.annot, (Printf.sprintf "Identifier %s was already present in the global scope" iname)))

(* Initializes the global scope getting the components of the program and their definitions *)
let rec get_components sym_tab components =
  (* Initialize the the symbol table of the used interfaces of a component *)
  let rec get_uses uses_sym_tab uses cname cloc = 
    match uses with
    | [] -> uses_sym_tab
    | iname::t ->
      if iname = "App" then 
        raise (Semantic_error(cloc, "The interface App cannot be used by a component"))
      else
      try
        let sym = (Symbol_table.lookup iname sym_tab) in
          match sym with
          | Interface_sym(_, _, _, _) -> get_uses (Symbol_table.add_entry iname sym uses_sym_tab) t cname cloc
          | Component_sym(identifier, _, _, _, _, _) -> raise (Semantic_error(cloc, Printf.sprintf "%s is not an interface identifier, component identifiers are not admitted in uses list" identifier))
          | _ -> ignore ()
      with
        | Symbol_table.NotFound( _ ) -> raise (Semantic_error(cloc, Printf.sprintf "In %s uses list was found an undefined interface %s" cname iname))
        | Symbol_table.DuplicateEntry( _ ) -> raise (Semantic_error(cloc, Printf.sprintf "The interface identifier %s is duplicated in componet %s uses list" iname cname))
    in
    (* Initialize the the symbol table of the provided interfaces of a component *)
    let rec get_provides provides_sym_tab provides cname cloc = 
      match provides with
      | [] -> provides_sym_tab
      | iname::t -> 
        if iname = "Prelude" then 
          raise (Semantic_error(cloc, "The interface Prelude cannot be provided by a component"))
        else
          try
            let sym = (Symbol_table.lookup iname sym_tab) in
              match sym with
              | Interface_sym(_, _, _, _) -> get_provides (Symbol_table.add_entry iname sym provides_sym_tab) t cname cloc
              | Component_sym(identifier, _, _, _, _, _) -> raise (Semantic_error(cloc, Printf.sprintf "%s is not an interface identifier, component identifiers are not admitted in provides list" identifier))
              | _ -> ignore ()
          with
            | Symbol_table.NotFound(_) -> raise (Semantic_error(cloc, Printf.sprintf "In %s provides list was found an undefined interface %s" cname iname))
            | Symbol_table.DuplicateEntry(_) -> raise (Semantic_error(cloc, Printf.sprintf "The interface identifier %s is duplicated in componet %s provides list" iname cname))
      in
      (* Gets the definitions of a component *)
      let rec get_definitions comp_sym_tab definitions = 
        match definitions with
        | [] -> comp_sym_tab
        | member::t ->
          match member.Ast.node with
          | Ast.VarDecl(vname, typ) ->
            begin
              match typ with
              | Ast.TVoid -> raise (Semantic_error(member.Ast.annot, "Cannot be defined a variable of type void"))
              | Ast.TArray(Ast.TArray(_, _), _) -> raise (Semantic_error(member.Ast.annot, "Multidimensional array are not allowed"))
              | Ast.TArray(Ast.TVoid, _) -> raise (Semantic_error(member.Ast.annot, "Cannot be defined an array of type void"))
              | Ast.TArray(_, None) -> raise (Semantic_error(member.Ast.annot, "Array references can occur only as formal parameters"))
              | Ast.TArray(_, Some n) when n < 1 -> raise (Semantic_error(member.Ast.annot, "Array should have a size of at least 1 element"))
              | Ast.TRef(typ) when (is_not_scalar typ) -> raise (Semantic_error(member.Ast.annot, "References T& requires that T is a scalar type"))
              | _ ->
                try
                  get_definitions (Symbol_table.add_entry vname (Var_sym(vname, typ, member.Ast.annot)) comp_sym_tab) t
                with Symbol_table.DuplicateEntry(_) ->
                  raise (Semantic_error(member.Ast.annot, Printf.sprintf "The variable %s was already declared in this scope" vname))
            end
            | Ast.FunDecl({Ast.rtype; Ast.fname; Ast.formals; _}) -> 
              match rtype with
              | Ast.TInt | Ast.TBool | Ast.TChar | Ast.TVoid -> 
                begin
                  let rec get_formals sym_tab = function
                    | [] -> sym_tab
                    | h::t ->
                      let (id, typ) = h in
                        match typ with
                        | Ast.TVoid -> raise (Semantic_error(member.Ast.annot, "A formal parameter cannot be of type void"))
                        | Ast.TArray(Ast.TArray(_, _), _) -> raise (Semantic_error(member.Ast.annot, "Multidimensional array are not allowed"))
                        | Ast.TArray(Ast.TVoid, _) -> raise (Semantic_error(member.Ast.annot, "A formal parameter cannot be an array of type void"))
                        | Ast.TArray(_, Some _) -> raise (Semantic_error(member.Ast.annot, "Array references does not require a size"))
                        | Ast.TRef(typ) when (is_not_scalar typ) -> raise (Semantic_error(member.Ast.annot, "References T& requires that T is a scalar type"))
                        | _ ->
                          try
                            get_formals (Symbol_table.add_entry id (Var_sym(id, typ, member.Ast.annot)) sym_tab) t
                          with Symbol_table.DuplicateEntry(_) ->
                            raise (Semantic_error(member.Ast.annot, Printf.sprintf "There are multiple formal parameters with identifier %s" id))
                  in
                    try
                      let sym_tab_function = get_formals (Symbol_table.begin_block Symbol_table.empty_table) formals in
                      let f_sym = Fun_sym(fname, Ast.TFun((List.map snd formals), rtype), sym_tab_function, member.Ast.annot) in 
                        get_definitions (Symbol_table.add_entry fname f_sym comp_sym_tab) t
                    with Symbol_table.DuplicateEntry(_) -> 
                      raise (Semantic_error(member.Ast.annot, Printf.sprintf "The function %s was already declared in this scope" fname))
                end
              | _ -> raise (Semantic_error(member.Ast.annot, "Functions can only returns values of type: int, bool, char, void"))
      in
  match components with
  | [] -> sym_tab
  | h::t ->
      match h.Ast.node with
      | Ast.ComponentDecl({ cname; uses; provides; definitions }) ->
          let comp_uses_sym_tab = get_uses (Symbol_table.begin_block Symbol_table.empty_table) ("Prelude"::uses) cname h.Ast.annot in
          let comp_provides_sym_tab = get_provides (Symbol_table.begin_block Symbol_table.empty_table) provides cname h.Ast.annot in
          let comp_sym_tab = get_definitions (Symbol_table.begin_block Symbol_table.empty_table) definitions in
          try
            get_components (Symbol_table.add_entry cname (Component_sym(cname, Ast.TComponent(cname), comp_sym_tab, comp_uses_sym_tab, comp_provides_sym_tab, h.Ast.annot)) sym_tab) t
          with Symbol_table.DuplicateEntry(_) ->
            raise (Semantic_error(h.Ast.annot, (Printf.sprintf "Identifier %s was already present in the global scope" cname)))

(* This function makes checks on the correctenss of a component  *)
let check_components sym_tab components interfaces =
  (* Given a name of an interface returns its declarations *)
  let rec get_interface_declarations inter_name interfaces = 
    match interfaces with
    | [] -> ignore ()
    | h::t -> 
      match h.Ast.node with
      | Ast.InterfaceDecl({ iname; declarations }) -> if inter_name = iname then declarations else get_interface_declarations inter_name t
  in
  (* Performs checks in order to ensure the correctness of the semantic rules for the provided interfaces of a component *)
  let rec check_component_provides sym_tab components interfaces =
    match components with
    | [] -> sym_tab
    | comp_decl::t ->
      match comp_decl.Ast.node with
      | Ast.ComponentDecl({ cname; provides; _ }) ->
        let comp_sym_tab = (match (Symbol_table.lookup cname sym_tab) with | Component_sym(_, _, comp_sym_tab, _, _, _) -> comp_sym_tab | _ -> ignore ()) in
        let rec check_members provides = 
          match provides with
          | [] -> sym_tab
          | iname::t ->
            let inter_sym_tab = (match (Symbol_table.lookup iname sym_tab) with | Interface_sym(_, _, sym_tab, _) -> sym_tab | _ -> ignore ()) in
            let interface_declarations = get_interface_declarations iname interfaces in
            let rec aux declarations = 
              match declarations with
              | [] -> []
              | h::t ->
                match h.Ast.node with
                | Ast.VarDecl(v_id, typ) ->
                  begin
                    try
                      match Symbol_table.lookup v_id comp_sym_tab with
                      | Var_sym(_, typ_, loc) ->
                        if Ast.equal_typ typ typ_ then aux t
                        else raise (Semantic_error(loc, Printf.sprintf "The type of variable %s, does not match with the one defined in the provided interface %s" v_id iname))
                      | _ -> ignore ()
                    with Symbol_table.NotFound(_) ->
                      raise (Semantic_error(h.Ast.annot, Printf.sprintf "The variable %s defined in the provided interface %s is not defined in component %s" v_id iname cname))
                  end
                  | Ast.FunDecl({ Ast.fname; _ }) ->
                    begin
                      let typ_in_inter = (match Symbol_table.lookup fname inter_sym_tab with | Fun_sym(_, typ, _, _) -> typ | _ -> ignore ()) in
                      try
                        let (typ_in_comp, loc) = (match Symbol_table.lookup fname comp_sym_tab with | Fun_sym(_, typ, _, loc) -> (typ, loc) | _ -> ignore ()) in
                          if Ast.equal_typ typ_in_inter typ_in_comp then aux t
                          else raise (Semantic_error(loc, Printf.sprintf "The type of function %s, does not match with the one defined in the provided interface %s" fname iname))
                      with Symbol_table.NotFound(_) ->
                        raise (Semantic_error(h.Ast.annot, Printf.sprintf "The function %s defined in the provided interface %s is not defined in component %s" fname iname cname))
                      
                    end
            in
              let _ = aux interface_declarations in
                check_members t
      in
        let _ = check_members provides in 
          check_component_provides sym_tab t interfaces
  in
  (* Performs checks in order to ensure the correctness of the semantic rules for the used interfaces of a component *)
  let rec check_component_uses sym_tab components interfaces =
    match components with
    | [] -> sym_tab
    | comp_decl::t ->
      match comp_decl.Ast.node with
      | Ast.ComponentDecl({ cname; uses; _ }) ->
        let comp_sym_tab = (match (Symbol_table.lookup cname sym_tab) with | Component_sym(_, _, comp_sym_tab, _, _, _) -> comp_sym_tab | _ -> ignore ()) in
        let rec check_members uses = 
          match uses with
          | [] -> sym_tab
          | iname::t ->
            let interface_declarations = get_interface_declarations iname interfaces in
            let rec aux declarations =
              match declarations with
              | [] -> []
              | h::t ->
                match h.Ast.node with
                | Ast.VarDecl(v_id, _) ->
                  begin
                    try
                      match Symbol_table.lookup v_id comp_sym_tab with
                      | Var_sym(_, _, loc) -> raise (Semantic_error(loc, Printf.sprintf "Inside interface %s there is declared a variable with identifier %s" iname v_id))
                      | Fun_sym(_, _, _,loc) -> raise (Semantic_error(loc, Printf.sprintf "Inside interface %s there is declared a function with identifier %s" iname v_id))
                      | _ -> ignore ()
                    with Symbol_table.NotFound(_) ->
                      h::(aux t)
                  end
                | Ast.FunDecl({ Ast.fname; _ }) ->
                  begin
                    try
                      match Symbol_table.lookup fname comp_sym_tab with
                      | Var_sym(_, _, loc) -> raise (Semantic_error(loc, Printf.sprintf "Inside interface %s there is declared a variable with identifier %s" iname fname))
                      | Fun_sym(_, _, _,loc) -> raise (Semantic_error(loc, Printf.sprintf "Inside interface %s there is declared a function with identifier %s" iname fname))
                      | _ -> ignore ()
                    with Symbol_table.NotFound(_) ->
                      aux t
                  end
            in
              let _ = aux interface_declarations in
                check_members t
        in
          let _ = check_members ("Prelude"::uses) in 
            check_component_uses sym_tab t interfaces
in
  (* Creates an Ast node for the interface "App" *)
  let make_app_interf_decl_node = 
    let declarations_list list = 
      let map_fun = 
        fun (fname, ftyp) -> 
          match ftyp with
            | Ast.TFun(_, rtype) -> Ast.make_node (Ast.FunDecl({ Ast.rtype = rtype; Ast.fname = fname; Ast.formals = []; Ast.body = None })) Location.dummy_code_pos
            | _ -> ignore () 
      in
        List.map map_fun list
    in
      Ast.make_node (Ast.InterfaceDecl({ iname = "App"; declarations = (declarations_list Mcomp_stdlib.app_signature)})) (Location.dummy_code_pos)
  in  
  let _ = check_component_provides sym_tab components (make_app_interf_decl_node::interfaces) in
  (* Creates an Ast node for the interface "Prelude" *)
  let make_prelude_interf_decl_node = 
    let declarations_list list = 
      let map_fun = 
        fun (fname, ftyp) -> 
          match ftyp with
            | Ast.TFun(_, rtype) -> Ast.make_node (Ast.FunDecl({ Ast.rtype = rtype; Ast.fname = fname; Ast.formals = []; Ast.body = None })) Location.dummy_code_pos
            | _ -> ignore () 
      in
        List.map map_fun list
    in
      Ast.make_node (Ast.InterfaceDecl({ iname = "Prelude"; declarations = (declarations_list Mcomp_stdlib.prelude_signature)})) (Location.dummy_code_pos)
  in
    check_component_uses sym_tab components (make_prelude_interf_decl_node::interfaces)
        
(* Initializes the global symbol table *)
let create_global_table loc_ast =
  (* Retruns the number of components that provide the interface "App" *)
  let rec count_components_provides_app components counter =
    match components with
    | [] -> counter
    | h::t -> 
      match h.Ast.node with
      Ast.ComponentDecl({ provides; _ }) ->
        if List.mem "App" provides 
          then count_components_provides_app t (counter + 1)
          else count_components_provides_app t counter
  in
  let (interfaces, components) = (match loc_ast with Ast.CompilationUnit({ interfaces; components; _ }) -> (interfaces, components)) in
    let global_sym_tab = get_mcomp_stdlib (Symbol_table.begin_block Symbol_table.empty_table) in
    let global_sym_tab = get_interfaces global_sym_tab interfaces in
    let global_sym_tab = get_components global_sym_tab components in
    let global_sym_tab = check_components global_sym_tab components interfaces in
    let num_components_provides_app = count_components_provides_app components 0 in
      if num_components_provides_app = 0 then raise (Semantic_error(Location.dummy_code_pos, "There is no component that provides the App interface"))
      else if num_components_provides_app > 1 then raise (Semantic_error(Location.dummy_code_pos, "The App interface cannot be provided by more than one component"))
      else global_sym_tab

(* Analyses and annotates expressions *)
let rec check_expr ast_node sym_tab comp_ast_node comp_sym =
  match ast_node.Ast.node with
  | Ast.LV(lv) -> 
    let clv = check_lvalue lv sym_tab comp_ast_node comp_sym in 
      Ast.make_node (Ast.LV(clv)) (clv.Ast.annot)
  | Ast.Assign(lv, e) -> 
    let check_assign typ_l typ_r =
      match (typ_l, typ_r) with
      | (typ_l, typ_r) when (Ast.equal_typ typ_l typ_r) && not (is_not_scalar typ_l) -> true
      | (Ast.TArray(_), Ast.TArray(_)) -> false
      | (Ast.TRef(typ_l), Ast.TRef(typ_r)) when (Ast.equal_typ typ_l typ_r) && not (is_not_scalar typ_l) -> true
      | (Ast.TRef(typ_l), typ_r) when (Ast.equal_typ typ_l typ_r) && not (is_not_scalar typ_l) -> true
      | (typ_l, Ast.TRef(typ_r)) when (Ast.equal_typ typ_l typ_r) && not (is_not_scalar typ_l) -> true
      | (_, _) -> false
    in
    let clv = check_lvalue lv sym_tab comp_ast_node comp_sym in 
    let ce = check_expr e sym_tab comp_ast_node comp_sym in
      if (check_assign clv.Ast.annot ce.Ast.annot) then (Ast.make_node (Ast.Assign(clv, ce)) (clv.Ast.annot))
      else raise (Semantic_error(ast_node.Ast.annot, "This assignment is not allowed, type are not correct"))
  | Ast.ILiteral(i) -> Ast.make_node (Ast.ILiteral(i)) Ast.TInt
  | Ast.CLiteral(c) -> Ast.make_node (Ast.CLiteral(c)) Ast.TChar
  | Ast.BLiteral(b) -> Ast.make_node (Ast.BLiteral(b)) Ast.TBool
  | Ast.UnaryOp(Ast.Neg, e) ->
    begin
      let ce = check_expr e sym_tab comp_ast_node comp_sym in
        match ce.Ast.annot with
        | Ast.TInt -> Ast.make_node (Ast.UnaryOp(Ast.Neg, ce)) Ast.TInt
        | Ast.TRef(Ast.TInt) -> Ast.make_node (Ast.UnaryOp(Ast.Neg, ce)) (Ast.TRef(Ast.TInt))
        | _ -> raise (Semantic_error(e.Ast.annot, "Expected an int expression"))
    end
  | Ast.UnaryOp(Ast.Not, e) ->
    begin
      let ce = check_expr e sym_tab comp_ast_node comp_sym in
        match ce.Ast.annot with
        | Ast.TBool -> Ast.make_node (Ast.UnaryOp(Ast.Not, ce)) Ast.TBool
        | Ast.TRef(Ast.TBool) -> Ast.make_node (Ast.UnaryOp(Ast.Not, ce)) (Ast.TRef(Ast.TBool))
        | _ -> raise (Semantic_error(e.Ast.annot, "Expected an boolean expression"))
    end
  | Ast.Address(lv) ->
    let clv = check_lvalue lv sym_tab comp_ast_node comp_sym in
      Ast.make_node (Ast.Address(clv)) (Ast.TRef(clv.Ast.annot))
  | Ast.BinaryOp(Ast.Add, e1, e2) ->
    let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
    let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
      begin
        match (ce1.Ast.annot, ce2.Ast.annot) with
          | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt) -> 
            Ast.make_node (Ast.BinaryOp(Ast.Add, ce1, ce2)) Ast.TInt
          | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type int or type &int"))
      end
  | Ast.BinaryOp(Ast.Sub, e1, e2) -> 
    let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
    let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
    begin
      match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt) -> 
          Ast.make_node (Ast.BinaryOp(Ast.Sub, ce1, ce2)) Ast.TInt
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type int or type &int"))
    end
  | Ast.BinaryOp(Ast.Mult, e1, e2) ->
    let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
    let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
    begin
      match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt) -> 
          Ast.make_node (Ast.BinaryOp(Ast.Mult, ce1, ce2)) Ast.TInt
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type int or type &int"))
    end
  | Ast.BinaryOp(Ast.Div, e1, e2) ->
    let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
    let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
    begin
      match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt) -> 
          Ast.make_node (Ast.BinaryOp(Ast.Div, ce1, ce2)) Ast.TInt
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type int or type &int"))
    end
  | Ast.BinaryOp(Ast.Mod, e1, e2) ->
    let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
    let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
    begin
      match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt) -> 
          Ast.make_node (Ast.BinaryOp(Ast.Mod, ce1, ce2)) Ast.TInt
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type int or type &int"))
    end
  | Ast.BinaryOp(Ast.Less, e1, e2) ->
    let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
    let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
    begin
      match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt) -> 
          Ast.make_node (Ast.BinaryOp(Ast.Less, ce1, ce2)) Ast.TBool
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type int or type &int"))
    end
  | Ast.BinaryOp(Ast.Leq, e1, e2) ->
    let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
    let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
    begin
      match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt) -> 
          Ast.make_node (Ast.BinaryOp(Ast.Leq, ce1, ce2)) Ast.TBool
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type int or type &int"))
    end
  | Ast.BinaryOp(Ast.Greater, e1, e2) ->
    let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
    let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
    begin
      match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt) -> 
          Ast.make_node (Ast.BinaryOp(Ast.Greater, ce1, ce2)) Ast.TBool
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type int or type &int"))
    end
    | Ast.BinaryOp(Ast.Geq, e1, e2) ->
      let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
      let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
      begin
        match (ce1.Ast.annot, ce2.Ast.annot) with
          | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt) -> 
            Ast.make_node (Ast.BinaryOp(Ast.Geq, ce1, ce2)) Ast.TBool
          | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type int or type &int"))
      end
    | Ast.BinaryOp(Ast.And, e1, e2) ->
      let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
      let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
      begin
        match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TBool, Ast.TBool) | (Ast.TRef(Ast.TBool), Ast.TRef(Ast.TBool)) | (Ast.TBool, Ast.TRef(Ast.TBool)) | (Ast.TRef(Ast.TBool), Ast.TBool) -> 
          Ast.make_node (Ast.BinaryOp(Ast.And, ce1, ce2)) Ast.TBool
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type bool or type &bool"))
      end
    | Ast.BinaryOp(Ast.Or, e1, e2) ->
      let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
      let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
      begin
        match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TBool, Ast.TBool) | (Ast.TRef(Ast.TBool), Ast.TRef(Ast.TBool)) | (Ast.TBool, Ast.TRef(Ast.TBool)) | (Ast.TRef(Ast.TBool), Ast.TBool) -> 
          Ast.make_node (Ast.BinaryOp(Ast.Or, ce1, ce2)) Ast.TBool
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "The two operands must be of type bool or type &bool"))
      end
    | Ast.BinaryOp(Ast.Equal, e1, e2) ->
      let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
      let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
      begin
        match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt)
        | (Ast.TBool, Ast.TBool) | (Ast.TRef(Ast.TBool), Ast.TRef(Ast.TBool)) | (Ast.TBool, Ast.TRef(Ast.TBool)) | (Ast.TRef(Ast.TBool), Ast.TBool) ->
          Ast.make_node (Ast.BinaryOp(Ast.Equal, ce1, ce2)) Ast.TBool
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "Operands are not well typed in this expression"))
      end
    | Ast.BinaryOp(Ast.Neq, e1, e2) ->
      let ce1 = check_expr e1 sym_tab comp_ast_node comp_sym in
      let ce2 = check_expr e2 sym_tab comp_ast_node comp_sym in 
      begin
        match (ce1.Ast.annot, ce2.Ast.annot) with
        | (Ast.TInt, Ast.TInt) | (Ast.TRef(Ast.TInt), Ast.TRef(Ast.TInt)) | (Ast.TInt, Ast.TRef(Ast.TInt)) | (Ast.TRef(Ast.TInt), Ast.TInt)
        | (Ast.TBool, Ast.TBool) | (Ast.TRef(Ast.TBool), Ast.TRef(Ast.TBool)) | (Ast.TBool, Ast.TRef(Ast.TBool)) | (Ast.TRef(Ast.TBool), Ast.TBool) ->
          Ast.make_node (Ast.BinaryOp(Ast.Neq, ce1, ce2)) Ast.TBool
        | _ -> raise (Semantic_error(ast_node.Ast.annot, "Operands are not well typed in this expression"))
      end
  | Ast.Call(None, fun_id, actual_params) ->
    let check_call inter_id_opt fun_typ =
      let rec get_actual_params_type = function
        | [] -> []
        | e::t -> 
          let ce = check_expr e sym_tab comp_ast_node comp_sym in
            match ce.Ast.annot with
            | Ast.TArray(typ, _) -> (Ast.TArray(typ, None))::(get_actual_params_type t)
            | _ -> (ce.Ast.annot)::(get_actual_params_type t)
      in
        match fun_typ with
        | Ast.TFun(formal_params_type, rtype) -> 
          let actual_params_type = get_actual_params_type actual_params in
            if (List.length actual_params_type) = (List.length formal_params_type) then
              let rec check_params_type formals actuals =
                match (formals, actuals) with
                | ([], []) -> Ast.make_node (Ast.Call(inter_id_opt, fun_id, (List.map (fun x -> check_expr x sym_tab comp_ast_node comp_sym) actual_params))) rtype
                | (h1::t1, h2::t2) when (Ast.equal_typ h1 h2) -> check_params_type t1 t2
                | (h1::t1, Ast.TRef(h2)::t2) when (Ast.equal_typ h1 h2) -> check_params_type t1 t2
                | _ -> raise (Semantic_error(ast_node.Ast.annot, Printf.sprintf "Parameters with not matching type are provided in the call of the function %s" fun_id))
              in
                check_params_type formal_params_type actual_params_type
            else
              raise (Semantic_error(ast_node.Ast.annot, Printf.sprintf "Function %s expects %d parameters, but %d are provided" fun_id (List.length formal_params_type) (List.length actual_params_type)))

      | _ -> ignore ()
    in
    begin
      try
        match Symbol_table.lookup fun_id sym_tab with
        | Var_sym(_, _, _) -> raise (Semantic_error(ast_node.Ast.annot, Printf.sprintf "%s is an identifier of a variable" fun_id))
        | _ -> ignore ()
      with Symbol_table.NotFound(_) ->
        let (comp_sym_tab, comp_uses_sym_tab) = (match comp_sym with | Component_sym(_, _, comp_sym_tab, comp_uses_sym_tab, _, _) -> (comp_sym_tab, comp_uses_sym_tab) | _ -> ignore ()) in
        let uses = (match comp_ast_node with | Ast.ComponentDecl({ uses; _ }) -> uses) in
        try
          match Symbol_table.lookup fun_id comp_sym_tab with
          | Var_sym(_, _, _) -> raise (Semantic_error(ast_node.Ast.annot, Printf.sprintf "%s is an identifier of a variable" fun_id))
          | Fun_sym(_, fun_typ, _, _) -> check_call None fun_typ
          | _ -> ignore ()
        with Symbol_table.NotFound(_) ->
          let rec search_fun_in_uses uses =
            match uses with
            | [] -> raise (Semantic_error(ast_node.Ast.annot, Printf.sprintf "Function %s is not defined" fun_id))
            | h::t ->
              match Symbol_table.lookup h comp_uses_sym_tab with
              | Interface_sym(_, _, inter_sym_tab, _) ->
                begin
                  try
                    match Symbol_table.lookup fun_id inter_sym_tab with
                    | Var_sym(_, _, _) -> raise (Semantic_error(ast_node.Ast.annot, Printf.sprintf "%s is an identifier of a variable" fun_id))
                    | Fun_sym(_, fun_typ, _, _) -> check_call (Some h) fun_typ
                    | _ -> ignore ()
                  with Symbol_table.NotFound(_) ->
                    search_fun_in_uses t
                end
              | _ -> ignore ()
          in
            search_fun_in_uses ("Prelude"::uses)
    end
  | Ast.IncDec(lv, ido) ->
    let clv = check_lvalue lv sym_tab comp_ast_node comp_sym in 
      begin
        match clv.Ast.annot with
        | Ast.TInt -> Ast.make_node (Ast.IncDec(clv, ido)) Ast.TInt
        | _ -> raise (Semantic_error(lv.Ast.annot, "Increment/Decrement operators require integer variables"))
      end
  | _ -> ignore ()

(* Analyses and annotates lvalues *)
and check_lvalue ast_node sym_tab comp_ast_node comp_sym =
  match ast_node.Ast.node with
  | Ast.AccVar(None, id) ->
    begin
      try
        match Symbol_table.lookup id sym_tab with
        | Var_sym(_, typ, _) -> Ast.make_node (Ast.AccVar(None, id)) typ
        | _ -> raise (Semantic_error(ast_node.Ast.annot, Printf.sprintf "%s is not a variable identifier" id))
      with Symbol_table.NotFound(_) ->
          let (comp_sym_tab, comp_uses_sym_tab) = (match comp_sym with | Component_sym(_, _, comp_sym_tab, comp_uses_sym_tab, _, _) -> (comp_sym_tab, comp_uses_sym_tab) | _ -> ignore ()) in
            try
              match Symbol_table.lookup id comp_sym_tab with
              | Var_sym(_, typ, _) -> Ast.make_node (Ast.AccVar(None, id)) typ
              | _ -> raise (Semantic_error(ast_node.Ast.annot, Printf.sprintf "%s is not a variable identifier" id))
            with Symbol_table.NotFound(_) ->
              match comp_ast_node with
              | Ast.ComponentDecl({ uses; _; }) ->
                  let rec find_var_in_uses uses =
                    match uses with
                    | [] -> raise (Semantic_error(ast_node.Ast.annot, Printf.sprintf "Variable %s not defined" id))
                    | h::t ->
                      match Symbol_table.lookup h comp_uses_sym_tab with
                      | Interface_sym(_, _, int_sym_tab, _) -> 
                        begin
                          try
                            match Symbol_table.lookup id int_sym_tab with
                              | Var_sym(_, typ, _) -> Ast.make_node (Ast.AccVar(Some h, id)) typ
                              | _ -> raise (Semantic_error(ast_node.Ast.annot, Printf.sprintf "%s is not a variable identifier" id))
                          with Symbol_table.NotFound(_) ->
                            find_var_in_uses t
                        end
                      | _ -> ignore ()
                  in
                    find_var_in_uses uses
      end
  | Ast.AccVar(Some _, _) -> ignore ()
  | Ast.AccIndex(lv, e) ->
    let ce = check_expr e sym_tab comp_ast_node comp_sym in
      match ce.Ast.annot with
      | Ast.TInt ->
        begin
          let clv = check_lvalue lv sym_tab comp_ast_node comp_sym in 
            match clv.Ast.annot with
            | Ast.TArray(t, _) ->
              begin
                if not(is_not_scalar t) then Ast.make_node (Ast.AccIndex(clv, ce)) t
                else raise (Semantic_error(lv.Ast.annot, "Type of the left value not admitted"))
              end
            | Ast.TRef(Ast.TArray(t, _)) ->
              begin
                if not(is_not_scalar t) then Ast.make_node (Ast.AccIndex(clv, ce)) t
                else raise (Semantic_error(lv.Ast.annot, "Type of the left value not admitted"))
              end
            | _ -> ignore ()
        end
      | _ -> raise (Semantic_error(e.Ast.annot, "Expected an integer expression"))

(* Analyses and annotates statements *)
and check_stmt ast_node sym_tab comp_ast_node comp_sym fun_rtype =
  match ast_node.Ast.node with
  | Ast.If(e, s1, s2) ->
    begin
      let ce = check_expr e sym_tab comp_ast_node comp_sym in 
        match ce.Ast.annot with
        | Ast.TBool -> 
          let cs1 = check_stmt s1 (Symbol_table.begin_block sym_tab) comp_ast_node comp_sym fun_rtype in
          let cs2 = check_stmt s2 (Symbol_table.begin_block sym_tab) comp_ast_node comp_sym fun_rtype in
            Ast.make_node (Ast.If(ce, cs1, cs2)) Ast.TVoid
        | _ -> raise (Semantic_error((ast_node.Ast.annot), "The if guard is not a boolean expression"))
    end
  | Ast.While(e, s) ->
    begin
      let ce = check_expr e sym_tab comp_ast_node comp_sym in 
        match ce.Ast.annot with
        | Ast.TBool -> 
          let cs = check_stmt s (Symbol_table.begin_block sym_tab) comp_ast_node comp_sym fun_rtype in
          Ast.make_node (Ast.While(ce, cs)) Ast.TVoid
      | _ -> raise (Semantic_error((ast_node.Ast.annot), "The while guard is not a boolean expression"))
    end
  | Ast.DoWhile(e, s) ->
    begin
      let cs = check_stmt s (Symbol_table.begin_block sym_tab) comp_ast_node comp_sym fun_rtype in
      let ce = check_expr e sym_tab comp_ast_node comp_sym in 
      match ce.Ast.annot with
        | Ast.TBool -> 
          Ast.make_node (Ast.DoWhile(ce, cs)) Ast.TVoid
      | _ -> raise (Semantic_error((ast_node.Ast.annot), "The do-while guard is not a boolean expression"))
    end
  | Ast.For(e1, e2, e3, s) ->
    begin
      let ce1 = match e1 with | None -> None | Some e1 -> Some (check_expr e1 sym_tab comp_ast_node comp_sym) in 
      let ce3 = match e3 with | None -> None | Some e3 -> Some (check_expr e3 sym_tab comp_ast_node comp_sym) in
      let cs = check_stmt s (Symbol_table.begin_block sym_tab) comp_ast_node comp_sym fun_rtype in
      match e2 with
      | None -> Ast.make_node (Ast.For(ce1, Some (Ast.make_node (Ast.BLiteral(true)) Ast.TBool), ce3, cs)) Ast.TVoid
      | Some e ->
          let ce2 = check_expr e sym_tab comp_ast_node comp_sym in
            match ce2.Ast.annot with
            | Ast.TBool -> Ast.make_node (Ast.For(ce1, Some ce2, ce3, cs)) Ast.TVoid
            | _ -> raise (Semantic_error((ast_node.Ast.annot), "The for guard is not a boolean expression"))
    end
  | Ast.Expr(e) ->
    let ce = check_expr e sym_tab comp_ast_node comp_sym in
      Ast.make_node (Ast.Expr(ce)) (ce.Ast.annot)
  | Ast.Return(e_opt) ->
    begin
      match e_opt with
      | None -> Ast.make_node (Ast.Return(None)) Ast.TVoid
      | Some e ->
        let ce = check_expr e sym_tab comp_ast_node comp_sym in
        if Ast.equal_typ fun_rtype ce.Ast.annot then (Ast.make_node (Ast.Return(Some ce)) ce.Ast.annot)
        else raise (Semantic_error(e.Ast.annot, "The type of this expression does not match the return type of the function"))
    end
  | Ast.Block(s_l) ->
    let rec check_block sym_tab = function
      | [] -> []
      | h::t ->
        let new_sym_tab =
          match h.Ast.node with
            | Ast.LocalDecl(id, typ) -> 
              begin
              try
                Symbol_table.add_entry id (Var_sym(id, typ, h.Ast.annot)) sym_tab
              with Symbol_table.DuplicateEntry(_) ->
                raise (Semantic_error((h.Ast.annot), Printf.sprintf "Identifier %s already defined in this scope" id))
              end
            | Ast.Stmt(_) -> sym_tab
          in
        (check_stmtordec h new_sym_tab comp_ast_node comp_sym fun_rtype)::(check_block sym_tab t)
    in 
      Ast.make_node (Ast.Block((check_block (Symbol_table.begin_block sym_tab) s_l))) Ast.TVoid
  | Ast.Skip -> Ast.make_node Ast.Skip Ast.TVoid

(* Analyses and annotates stmtordec nodes *)
and check_stmtordec ast_node sym_tab comp_ast_node comp_sym fun_rtype = 
  match ast_node.Ast.node with
  | Ast.LocalDecl(vname, typ) ->
    begin
      match typ with
      | Ast.TVoid -> raise (Semantic_error(ast_node.Ast.annot, "Cannot be defined a variable of type void"))
      | Ast.TArray(Ast.TArray(_, _), _) -> raise (Semantic_error(ast_node.Ast.annot, "Multidimensional array are not allowed"))
      | Ast.TArray(Ast.TVoid, _) -> raise (Semantic_error(ast_node.Ast.annot, "Cannot be defined an array of type void"))
      | Ast.TArray(_, None) -> raise (Semantic_error(ast_node.Ast.annot, "Array references can occur only as formal parameters"))
      | Ast.TArray(_, Some n) when n < 1 -> raise (Semantic_error(ast_node.Ast.annot, "Array should have a size of at least 1 element"))
      | Ast.TRef(typ) when (is_not_scalar typ) -> raise (Semantic_error(ast_node.Ast.annot, "References T& requires that T is a scalar type"))
      | _ -> Ast.make_node (Ast.LocalDecl(vname, typ)) typ
    end
  | Ast.Stmt(s) -> 
    let cs = check_stmt s sym_tab comp_ast_node comp_sym fun_rtype in
      Ast.make_node (Ast.Stmt(cs)) Ast.TVoid

let type_check loc_ast = 
  let sym_tab = create_global_table loc_ast in (* Global symbol table *)
    let (inter, comp, conn) = (match loc_ast with Ast.CompilationUnit({ interfaces; components; connections; }) -> (interfaces, components, connections)) in
      let rec annotate_interfaces interfaces =
        let rec annotate_interface_declarations declarations =
          match declarations with
          | [] -> []
          | h::t ->
            match h.Ast.node with
              | Ast.VarDecl(vname, typ) -> (Ast.make_node (Ast.VarDecl(vname, typ)) typ)::(annotate_interface_declarations t)
              | Ast.FunDecl({ Ast.body = Some _; _ }) -> ignore ()
              | Ast.FunDecl({ Ast.rtype; Ast.fname; Ast.formals; body = None }) ->
                (Ast.make_node (Ast.FunDecl({ Ast.rtype; fname; formals; body = None })) (Ast.TFun(List.map snd formals, rtype)))::(annotate_interface_declarations t)
        in
          match interfaces with
          | [] -> []
          | h::t ->
            match h.Ast.node with
            | Ast.InterfaceDecl({ iname; declarations }) ->
              (Ast.make_node (Ast.InterfaceDecl({ iname; declarations = (annotate_interface_declarations declarations) })) (Ast.TInterface(iname)))::(annotate_interfaces t)
      in
      let rec annotate_components components =
        let rec annotate_component_definitions definitions comp_sym comp_sym_tab comp_ast_node = 
          match definitions with
          | [] -> []
          | h::t ->
            match h.Ast.node with
            | Ast.VarDecl(vname, typ) -> (Ast.make_node (Ast.VarDecl(vname, typ)) typ)::(annotate_component_definitions t comp_sym comp_sym_tab comp_ast_node)
            | Ast.FunDecl({ Ast.rtype; Ast.fname; Ast.formals; Ast.body }) ->
              match body with
              | None -> ignore ()
              | Some body ->
                match Symbol_table.lookup fname comp_sym_tab with
                | Fun_sym(_, _, fun_sym_tab, _) ->
                  let cbody = check_stmt body fun_sym_tab comp_ast_node comp_sym rtype in
                  (Ast.make_node (Ast.FunDecl({ Ast.rtype = rtype; Ast.fname = fname; Ast.formals = formals; Ast.body = Some cbody; })) (Ast.TFun(List.map snd formals, rtype)))::(annotate_component_definitions t comp_sym comp_sym_tab comp_ast_node)
                | _ -> ignore ()
        in
          match components with
          | [] -> []
          | h::t ->
            match h.Ast.node with
            | Ast.ComponentDecl({ cname; uses; provides; definitions }) ->
              let comp_sym = Symbol_table.lookup cname sym_tab in
                match comp_sym with
                | Component_sym(_, _, comp_sym_tab, _, _ ,_) ->
                  (Ast.make_node (Ast.ComponentDecl({ cname; uses; provides; definitions = annotate_component_definitions definitions comp_sym comp_sym_tab h.Ast.node })) (Ast.TComponent(cname)))::(annotate_components t)
                | _ -> ignore ()
      in
        Ast.CompilationUnit{ interfaces = (annotate_interfaces inter); components = (annotate_components comp); connections = conn }