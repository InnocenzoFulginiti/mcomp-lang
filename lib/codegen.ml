let ignore () = failwith "* IGNORE *"
let llcontext = Llvm.global_context ()

let int_type = Llvm.i32_type llcontext
let bool_type = Llvm.i1_type llcontext
let char_type = Llvm.i8_type llcontext
let void_type = Llvm.void_type llcontext

(* This function converts a mcomp-lang type into the llvm type *)
let rec to_llvm_type typ = 
  match typ with
  | Ast.TInt -> int_type
  | Ast.TBool -> bool_type
  | Ast.TChar -> char_type
  | Ast.TArray(t, None) -> Llvm.pointer_type (to_llvm_type t)
  | Ast.TArray(t, Some n) -> Llvm.array_type (to_llvm_type t) n
  | Ast.TRef(t) -> Llvm.pointer_type (to_llvm_type t)
  | Ast.TVoid -> void_type
  | Ast.TFun(params_t, ret_t) ->
    let ret_type = to_llvm_type ret_t in 
    let params_type = Array.of_list (List.map (fun x -> to_llvm_type x) params_t) in 
      Llvm.function_type ret_type params_type
  | _ -> ignore ()

(* Given a type of a variable returns its corresponding default value *)
let rec default_value typ =
  match typ with
  | Ast.TInt -> Llvm.const_int int_type 0
  | Ast.TBool -> Llvm.const_int bool_type 0
  | Ast.TChar -> Llvm.const_int char_type 0
  | Ast.TRef(t) -> Llvm.const_pointer_null (to_llvm_type t)
  | Ast.TArray(t, Some n) ->
    let llt = to_llvm_type t in 
    let array_initializer = Array.init n (fun _ -> default_value t) in 
    Llvm.const_array llt array_initializer
  | _ -> ignore ()

(* Performs the mangling name with the given component *)
let mangling cname name = Printf.sprintf "_%s_%s" (String.lowercase_ascii cname) (String.lowercase_ascii name)

let rec codegen_expr ast_node llmodule ibuilder llfundef fun_sym_tab cname =
  match ast_node.Ast.node with
  | Ast.LV(l) -> codegen_lv_build_load l llmodule ibuilder llfundef fun_sym_tab cname
  | Ast.Assign(l, e) ->
    begin
      let ce = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in
        match e.Ast.node with
        | Ast.Address(_) ->
          let cl = codegen_lv_no_build_load l llmodule ibuilder llfundef fun_sym_tab cname true in
          let _ = Llvm.build_store ce cl ibuilder in 
            ce
        | _ ->
          let cl = codegen_lv_no_build_load l llmodule ibuilder llfundef fun_sym_tab cname false in
          let _ = Llvm.build_store ce cl ibuilder in 
            ce
    end
  | Ast.ILiteral(i) -> Llvm.const_int int_type i
  | Ast.CLiteral(c) -> Llvm.const_int char_type (int_of_char c)
  | Ast.BLiteral(b) -> Llvm.const_int bool_type (if b then 1 else 0)
  | Ast.UnaryOp(Ast.Neg, e) ->
    let ce = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in
      Llvm.build_neg ce "neg" ibuilder
  | Ast.UnaryOp(Ast.Not, e) ->
    let ce = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in
      Llvm.build_not ce "not" ibuilder
  | Ast.Address(l) -> codegen_lv_no_build_load l llmodule ibuilder llfundef fun_sym_tab cname true
  | Ast.BinaryOp(Ast.Add, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_add ce1 ce2 "add" ibuilder
  | Ast.BinaryOp(Ast.Sub, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_sub ce1 ce2 "sub" ibuilder
  | Ast.BinaryOp(Ast.Mult, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_mul ce1 ce2 "mult" ibuilder
  | Ast.BinaryOp(Ast.Div, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_sdiv ce1 ce2 "div" ibuilder
  | Ast.BinaryOp(Ast.Mod, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_srem ce1 ce2 "mod" ibuilder
  | Ast.BinaryOp(Ast.Equal, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_icmp Llvm.Icmp.Eq ce1 ce2 "eq" ibuilder
  | Ast.BinaryOp(Ast.Neq, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_icmp Llvm.Icmp.Ne ce1 ce2 "neq" ibuilder
  | Ast.BinaryOp(Ast.Less, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_icmp Llvm.Icmp.Slt ce1 ce2 "less" ibuilder
  | Ast.BinaryOp(Ast.Leq, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_icmp Llvm.Icmp.Sle ce1 ce2 "leq" ibuilder
  | Ast.BinaryOp(Ast.Greater, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_icmp Llvm.Icmp.Sgt ce1 ce2 "greater" ibuilder
  | Ast.BinaryOp(Ast.Geq, e1, e2) ->
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in 
      Llvm.build_icmp Llvm.Icmp.Sge ce1 ce2 "geq" ibuilder
  | Ast.BinaryOp(Ast.And, e1, e2) ->
    (* The AND operator is implemented with the short-circuit evaluation *)
    let bcontinue = Llvm.append_block llcontext "continue" llfundef in 
    let bend = Llvm.append_block llcontext "end" llfundef in
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let incoming_block1 = Llvm.insertion_block ibuilder in
    let _ = Llvm.build_cond_br ce1 bcontinue bend ibuilder in 
    Llvm.position_at_end bcontinue ibuilder;
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in
    let incoming_block2 = Llvm.insertion_block ibuilder in
    let _ = Llvm.build_br bend ibuilder in
    Llvm.position_at_end bend ibuilder;
    Llvm.build_phi [(ce1, incoming_block1); (ce2, incoming_block2)] "phi_and" ibuilder
  | Ast.BinaryOp(Ast.Or, e1, e2) ->
    (* The OR operator is implemented with the short-circuit evaluation *)
    let bcontinue = Llvm.append_block llcontext "continue" llfundef in 
    let bend = Llvm.append_block llcontext "end" llfundef in
    let ce1 = codegen_expr e1 llmodule ibuilder llfundef fun_sym_tab cname in
    let incoming_block1 = Llvm.insertion_block ibuilder in
    let _ = Llvm.build_cond_br ce1 bend bcontinue ibuilder in 
    Llvm.position_at_end bcontinue ibuilder;
    let ce2 = codegen_expr e2 llmodule ibuilder llfundef fun_sym_tab cname in
    let incoming_block2 = Llvm.insertion_block ibuilder in
    let _ = Llvm.build_br bend ibuilder in
    Llvm.position_at_end bend ibuilder;
    Llvm.build_phi [(ce1, incoming_block1); (ce2, incoming_block2)] "phi_or" ibuilder
  | Ast.Call(cname_opt, fname, e) ->
    begin
      match cname_opt with
      | None -> ignore ()
      | Some cname_ ->
        begin
          match Llvm.lookup_function (mangling cname_ fname) llmodule with
          | None -> ignore ()
          | Some llfun ->
            let ce = Array.of_list (List.map (fun e -> codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname) e) in
            begin
            match ast_node.Ast.annot with
            | Ast.TVoid -> Llvm.build_call llfun ce "" ibuilder
            | _ -> Llvm.build_call llfun ce (Printf.sprintf "call_%s" fname) ibuilder
            end 
        end
    end
  | Ast.IncDec(l, ido) ->
    let cl = codegen_lv_build_load l llmodule ibuilder llfundef fun_sym_tab cname in
    match ido with
    | Ast.PreInc ->
      let inc_val = Llvm.build_add cl (Llvm.const_int int_type 1) "pre_inc" ibuilder in
      let tmp = codegen_lv_no_build_load l llmodule ibuilder llfundef fun_sym_tab cname false in
      let _ = Llvm.build_store inc_val tmp ibuilder in 
        inc_val
    | Ast.PostInc ->
      let inc_val = Llvm.build_add cl (Llvm.const_int int_type 1) "pre_inc" ibuilder in
      let tmp = codegen_lv_no_build_load l llmodule ibuilder llfundef fun_sym_tab cname false in
      let _ = Llvm.build_store inc_val tmp ibuilder in 
        cl
    | Ast.PreDec ->
      let dec_val = Llvm.build_sub cl (Llvm.const_int int_type 1) "pre_inc" ibuilder in
      let tmp = codegen_lv_no_build_load l llmodule ibuilder llfundef fun_sym_tab cname false in
      let _ = Llvm.build_store dec_val tmp ibuilder in 
        dec_val
    | Ast.PostDec ->
      let dec_val = Llvm.build_sub cl (Llvm.const_int int_type 1) "pre_inc" ibuilder in
      let tmp = codegen_lv_no_build_load l llmodule ibuilder llfundef fun_sym_tab cname false in
      let _ = Llvm.build_store dec_val tmp ibuilder in 
        cl

and codegen_lv_build_load ast_node llmodule ibuilder llfundef fun_sym_tab cname = 
  let get_llval id qual = 
    match qual with
    | None -> 
      begin
        try
          Symbol_table.lookup id fun_sym_tab
        with Symbol_table.NotFound(_) ->
          Symbol_table.lookup (mangling cname id) fun_sym_tab
      end
    | Some cname_ ->
      Symbol_table.lookup (mangling cname_ id) fun_sym_tab
  in
  match ast_node.Ast.node with
  | Ast.AccVar(qual, id) ->
    begin
      let llval = get_llval id qual in
        match ast_node.Ast.annot with
        | Ast.TArray(_, Some _) -> Llvm.build_in_bounds_gep llval [| Llvm.const_int int_type 0; Llvm.const_int int_type 0 |] "in_bounds_gep" ibuilder
        | Ast.TRef(_) -> 
          let load = Llvm.build_load llval "load" ibuilder in 
            Llvm.build_load load "load" ibuilder
        | _ -> Llvm.build_load llval "load" ibuilder
    end
  | Ast.AccIndex(l, e) ->
    let ce = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in
    let llval =
      match l.Ast.node with
      | Ast.AccVar(qual, id) -> get_llval id qual
      | _ -> ignore ()
    in
      match l.Ast.annot with
      | Ast.TRef(_)
      | Ast.TArray(_, None) ->
        let load = Llvm.build_load llval "load" ibuilder in
        let llelement = Llvm.build_in_bounds_gep load [| ce |] "in_bounds_gep" ibuilder in 
          Llvm.build_load llelement "load" ibuilder
      | Ast.TArray(typ, Some _) -> 
        begin
        let llelement = Llvm.build_in_bounds_gep llval [| Llvm.const_int int_type 0; ce |] "in_bounds_gep" ibuilder in 
        let load = Llvm.build_load llelement "load" ibuilder in 
          match typ with
          | Ast.TRef(_) -> Llvm.build_load load "load" ibuilder
          | _ -> load
        end
      | _ -> ignore ()

and codegen_lv_no_build_load ast_node llmodule ibuilder llfundef fun_sym_tab cname address = 
  let get_llval id qual = 
    match qual with
    | None -> 
      begin
        try
          Symbol_table.lookup id fun_sym_tab
        with Symbol_table.NotFound(_) ->
          Symbol_table.lookup (mangling cname id) fun_sym_tab
      end
    | Some cname_ ->
      Symbol_table.lookup (mangling cname_ id) fun_sym_tab
  in
  match ast_node.Ast.node with
  | Ast.AccVar(qual, id) ->
    begin
      let llval = get_llval id qual in
        match ast_node.Ast.annot with
        | Ast.TArray(_, Some _) -> Llvm.build_in_bounds_gep llval [| Llvm.const_int int_type 0; Llvm.const_int int_type 0 |] "in_bounds_gep" ibuilder
        | Ast.TRef(_) -> 
          if address then llval else Llvm.build_load llval "load" ibuilder
        | _ -> llval
    end
  | Ast.AccIndex(l, e) ->
    let ce = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in
    let llval =
      match l.Ast.node with
      | Ast.AccVar(qual, id) -> get_llval id qual
      | _ -> ignore ()
    in
      match l.Ast.annot with
      | Ast.TRef(_)
      | Ast.TArray(_, None) ->
        let load = Llvm.build_load llval "load" ibuilder in
          Llvm.build_in_bounds_gep load [| ce |] "in_bounds_gep" ibuilder
      | Ast.TArray(_, Some _) -> Llvm.build_in_bounds_gep llval [| Llvm.const_int int_type 0; ce |] "in_bounds_gep" ibuilder
      | _ -> ignore ()

and codegen_stmt ast_node llmodule ibuilder llfundef fun_sym_tab cname = 
  match ast_node.Ast.node with
  | Ast.If(e, s1, s2) ->
    let bthen = Llvm.append_block llcontext "then" llfundef in 
    let belse = Llvm.append_block llcontext "else" llfundef in 
    let bcont = Llvm.append_block llcontext "cont" llfundef in 
    let ce1 = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in 
    let _ = Llvm.build_cond_br ce1 bthen belse ibuilder in 
    Llvm.position_at_end bthen ibuilder;
    let cs1 = codegen_stmt s1 llmodule ibuilder llfundef fun_sym_tab cname in 
      if not(cs1) 
        then let _ = Llvm.build_br bcont ibuilder in ()
        else ()
      ;
    Llvm.position_at_end belse ibuilder;
    let cs2 = codegen_stmt s2 llmodule ibuilder llfundef fun_sym_tab cname in 
      if not(cs2) 
        then let _ = Llvm.build_br bcont ibuilder in ()
        else ()
      ;
    Llvm.position_at_end bcont ibuilder;
    cs1 && cs2
  | Ast.While(e, s) ->
    let bguard = Llvm.append_block llcontext "guard" llfundef in 
    let btrue = Llvm.append_block llcontext "true" llfundef in 
    let bfalse = Llvm.append_block llcontext "false" llfundef in 
    let _ = Llvm.build_br bguard ibuilder in 
    Llvm.position_at_end bguard ibuilder;
    let ce = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in 
    let _ = Llvm.build_cond_br ce btrue bfalse ibuilder in 
    Llvm.position_at_end btrue ibuilder;
    let cs = codegen_stmt s llmodule ibuilder llfundef fun_sym_tab cname in 
      if not(cs)
        then let _ = Llvm.build_br bguard ibuilder in ()
        else ()
      ;
    Llvm.position_at_end bfalse ibuilder;
    cs
  | Ast.DoWhile(e, s) ->
    let bguard = Llvm.append_block llcontext "guard" llfundef in 
    let btrue = Llvm.append_block llcontext "true" llfundef in 
    let bfalse = Llvm.append_block llcontext "false" llfundef in 
    let _ = Llvm.build_br btrue ibuilder in 
    Llvm.position_at_end btrue ibuilder;
    let cs = codegen_stmt s llmodule ibuilder llfundef fun_sym_tab cname in 
      if not(cs)
        then let _ = Llvm.build_br bguard ibuilder in ()
        else ()
      ;
    Llvm.position_at_end bguard ibuilder;
    let ce = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in 
    let _ = Llvm.build_cond_br ce btrue bfalse ibuilder in 
    Llvm.position_at_end bfalse ibuilder;
    cs
  | Ast.For(e1, e2, e3, s) ->
    let bguard = Llvm.append_block llcontext "guard" llfundef in 
    let btrue = Llvm.append_block llcontext "true" llfundef in 
    let bfalse = Llvm.append_block llcontext "false" llfundef in 
    let _ =
      match e1 with
      | None -> ()
      | Some e -> let _ = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in ()
    in
    let _ = Llvm.build_br bguard ibuilder in 
    Llvm.position_at_end bguard ibuilder;
    let _ =
      match e2 with 
      | None -> ()
      | Some e -> 
        let ce = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in
        let _ = Llvm.build_cond_br ce btrue bfalse ibuilder in 
          ()
    in
      Llvm.position_at_end btrue ibuilder;
    let cs = codegen_stmt s llmodule ibuilder llfundef fun_sym_tab cname in
    let _ = 
      match e3 with
      | None -> ()
      | Some e -> let _ = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in ()
    in
      if not(cs)
        then let _ = Llvm.build_br bguard ibuilder in ()
        else ()
      ;
    Llvm.position_at_end bfalse ibuilder;
    cs
  | Ast.Expr(e) -> let _ = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in false;
  | Ast.Return(e) ->
    begin
      match e with
      | None -> let _ = Llvm.build_ret_void ibuilder in true
      | Some e ->
        let ce = codegen_expr e llmodule ibuilder llfundef fun_sym_tab cname in
        let _ = Llvm.build_ret ce ibuilder in true
    end
  | Ast.Block(s) ->
    let block_sym_tab = Symbol_table.begin_block fun_sym_tab in
      List.fold_left (fun b s -> (codegen_stmtordec s llmodule ibuilder llfundef block_sym_tab cname) || b) false s
  | Ast.Skip -> false

and codegen_stmtordec ast_node llmodule ibuilder llfundef fun_sym_tab cname =
  match ast_node.Ast.node with
  | Ast.LocalDecl(id, typ) ->
    let lltype = to_llvm_type typ in
    let llvalue = 
      match typ with
      | Ast.TArray(_, Some n) -> Llvm.build_array_alloca lltype (Llvm.const_int int_type n) id ibuilder
      | _ -> Llvm.build_alloca lltype id ibuilder
    in
    let _ = 
      Symbol_table.add_entry id llvalue fun_sym_tab in
        false
  | Ast.Stmt(s) -> codegen_stmt s llmodule ibuilder llfundef fun_sym_tab cname

let to_llvm_module ast =
  let sym_table = Symbol_table.begin_block Symbol_table.empty_table in
  let llmodule = Llvm.create_module llcontext "mcomp-module" in
  let _ = List.iter (fun (fname, typ) -> let _ = Llvm.declare_function (mangling "prelude" fname) (to_llvm_type typ) llmodule in ()) Mcomp_stdlib.prelude_signature in
  let _ = match ast with
    | Ast.CompilationUnit({ components; _ }) -> 
      (* Initialize the global module with the component definitions *)
      let rec get_components components = 
        match components with
        | [] -> ()
        | h::t -> match h.Ast.node with
          Ast.ComponentDecl({ cname; definitions; _ }) ->
            let rec get_definitions definitions =
              match definitions with
              | [] -> ()
              | h::t -> match h.Ast.node with
                | Ast.VarDecl(vname, typ) -> 
                  let vname_mang = mangling cname vname in
                  let def = Llvm.define_global vname_mang (default_value typ) llmodule in 
                  let _ = Symbol_table.add_entry vname_mang def sym_table in
                    get_definitions t
                | Ast.FunDecl({ Ast.fname; _ }) ->
                  let fname_mang = if fname = "main" then fname else mangling cname fname in 
                  let lltype = to_llvm_type h.Ast.annot in 
                  let def = Llvm.define_function fname_mang lltype llmodule in 
                  let _ = Symbol_table.add_entry fname_mang def sym_table in
                    get_definitions t
            in
              let _ = get_definitions definitions in 
                get_components t
      in
      let rec gen_components components = 
        match components with 
        | [] -> ()
        | h::t -> match h.Ast.node with
          Ast.ComponentDecl({ cname; definitions; _ }) ->
            let rec gen_fun_body definitions =
              match definitions with
              | [] -> ()
              | h::t -> match h.Ast.node with
                | Ast.VarDecl(_) -> gen_fun_body t
                | Ast.FunDecl({ Ast.fname; formals; body = Some body; rtype }) ->
                  (* Emits the LLVM code for the body of the function *)
                  let llfundef = if fname = "main" then (Symbol_table.lookup fname sym_table) else (Symbol_table.lookup (mangling cname fname) sym_table) in
                  let ibuilder = Llvm.builder_at_end llcontext (Llvm.entry_block llfundef) in
                  let list_of_int n = if n < 1 then [] else let rec aux l n = match n with 0 -> 0::l | x -> x::(aux l (x-1)) in aux [] (n - 1) |> List.rev in
                  let fun_sym_tab = 
                    List.fold_left (
                      fun fun_sym_tab ((id, typ), num) ->
                        let lltype = to_llvm_type typ in 
                        let param_stack = match typ with
                          | Ast.TArray(_, Some n) -> Llvm.build_array_alloca lltype (Llvm.const_int int_type n) id ibuilder
                          | _ -> Llvm.build_alloca lltype id ibuilder
                        in
                        let param = Llvm.param llfundef num in 
                        let _ = Llvm.build_store param param_stack ibuilder in 
                          Symbol_table.add_entry id param_stack fun_sym_tab
                    ) (Symbol_table.begin_block sym_table) (List.combine formals (list_of_int (List.length formals)))
                  in
                  let _ = codegen_stmt body llmodule ibuilder llfundef fun_sym_tab cname in
                  let _ =
                      (* Removes the instructions in a basic block after a return instruction *)
                      Llvm.iter_blocks 
                        (fun bb -> 
                          let delete = ref false in
                          let instr_to_delete = 
                            Llvm.fold_left_instrs 
                              (fun acc ins -> 
                                if !delete then
                                  ins::acc
                                else
                                  match Llvm.instr_opcode ins with
                                  | Llvm.Opcode.Ret -> let _ = delete := true in acc
                                  | _ -> acc
                              ) [] bb
                          in 
                            List.iter Llvm.delete_instruction instr_to_delete
                        ) 
                      llfundef
                  in
                  let _ =
                    match rtype with
                    | Ast.TVoid ->
                      (* Add a return void instruction in cases where it has been omitted *)
                      Llvm.iter_blocks
                        (fun bb ->
                          match Llvm.block_terminator bb with
                          | None ->
                            let _ = Llvm.position_at_end bb ibuilder in 
                            let _ = Llvm.build_ret_void ibuilder in 
                              ()
                          | Some _ -> ()
                        )
                        llfundef
                    | _ ->
                      let _ = 
                        (* Add a return instruction in cases where it has been omitted, the returned value is the default value of rtype *)
                        Llvm.iter_blocks
                        (fun bb ->
                          match Llvm.block_terminator bb with
                          | None ->
                            let _ = Llvm.position_at_end bb ibuilder in 
                            let _ = Llvm.build_ret (default_value rtype) ibuilder in 
                              ()
                          | Some _ -> ()
                        )
                        llfundef
                      in
                      (* Creates a unique return block in order to manage the cases in which there are more return instructions *)
                      let blocks = Llvm.fold_left_blocks (fun acc block -> block::acc) [] llfundef |> List.rev in
                      let bret = Llvm.append_block llcontext "ret_merge" llfundef in
                      let _ = Llvm.position_at_end bret ibuilder in
                      let phi = Llvm.build_empty_phi (to_llvm_type rtype) "phi_ret" ibuilder in 
                      let _ = Llvm.build_ret phi ibuilder in
                      List.iter
                        (fun bb ->
                          match Llvm.block_terminator bb with
                          | None -> ()
                          | Some instr -> 
                            match Llvm.instr_opcode instr with
                            | Llvm.Opcode.Ret ->
                              let ret_val = Llvm.operand instr 0 in
                              let _ = Llvm.delete_instruction instr in
                              let _ = Llvm.position_at_end bb ibuilder in 
                              let _ = Llvm.build_br bret ibuilder in 
                              let _ = Llvm.add_incoming (ret_val, bb) phi in 
                                ()
                            | _ -> ()
                        )
                        blocks
                  in 
                    gen_fun_body t
                | _ -> ignore ()
            in 
              let _ = gen_fun_body definitions in 
                gen_components t
      in
        let _ = get_components components in 
          gen_components components
  in
    llmodule