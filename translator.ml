open Xi_lib
open Ir
open String

let i32_0 = Int32.of_int 0
let i32_1 = Int32.of_int 1

(* --------------------------------------------------- *)

module Make() = struct

  module Environment = struct

    type env = Env of
      { procmap: procid Ast.IdMap.t
      ; varmap: reg Ast.IdMap.t
      }

    let empty =
      let procmap = Ast.IdMap.empty in
      let varmap = Ast.IdMap.empty in
      Env {procmap; varmap}


    let add_proc id procid (Env {procmap; varmap}) =
      let procmap = Ast.IdMap.add id procid procmap in
      Env {procmap; varmap}

    let add_var id reg (Env {procmap; varmap}) =
      let varmap = Ast.IdMap.add id reg varmap in
      Env {procmap; varmap}

    let lookup_proc id (Env {procmap; _}) =
      try
        Ast.IdMap.find id procmap
      with Not_found ->
        failwith @@ Format.sprintf "Unknown procedure identifier: %s" (Ast.string_of_identifier id)

    let lookup_var id (Env {varmap; _}) =
      try
        Ast.IdMap.find id varmap
      with Not_found ->
        failwith @@ Format.sprintf "Unknown variable identifier: %s" (Ast.string_of_identifier id)

  end


(* --------------------------------------------------- *)
  module Scanner = struct

    let mangle_id id =
      Format.sprintf "_I_%s" (Ast.string_of_identifier id)

    let rec mangle_texpr = function
      | Ast.TEXPR_Int _ -> "i"
      | Ast.TEXPR_Bool _ -> "b"
      | Ast.TEXPR_Array {sub;_} -> "a" ^ mangle_texpr sub


    let mangle_var_declaration v = mangle_texpr @@ Ast.type_expression_of_var_declaration v

    let mangle_formal_parameters xs = String.concat "" (List.map mangle_var_declaration xs)

    let mangle_return_types xs = String.concat "" (List.map mangle_texpr xs)

    let scan_global_declaration (env, symbols) = function
      | Ast.GDECL_Function {id; formal_parameters; return_types; _} ->
        let name = Format.sprintf "%s_%s_%s" 
          (mangle_id id) (mangle_formal_parameters formal_parameters) (mangle_return_types return_types)
          in
        
        Environment.add_proc id (Procid name) env, Procid name :: symbols

    let scan_module env (Ast.ModuleDefinition {global_declarations; _}) = 
      List.fold_left scan_global_declaration (env, []) global_declarations

  end
(* --------------------------------------------------- *)

  module type SContext = sig

    val cfg : ControlFlowGraph.t

    val node2type: (Ast.node_tag, Types.normal_type) Hashtbl.t

    val allocate_register: unit -> reg
  end

(* --------------------------------------------------- *)
  module Translator(M:SContext) = struct
    open M

    (* dodaj instrukcje do bloku *)
    let append_instruction l i =
      let block = ControlFlowGraph.block cfg l in
      ControlFlowGraph.set_block cfg l (block @ [i])

    (* ustaw terminator na skok bezwarunkowy *)
    let set_jump l_from l_to =
      ControlFlowGraph.set_terminator cfg l_from @@ T_Jump l_to;
      ControlFlowGraph.connect cfg l_from l_to

    (* ustaw terminator na powrót-z-procedury *)
    let set_return l_from xs =
      ControlFlowGraph.set_terminator cfg l_from @@ T_Return xs;
      ControlFlowGraph.connect cfg l_from (ControlFlowGraph.exit_label cfg)

    (* ustaw terminator na skok warunkowy *)
    let set_branch cond a b l_from l_to1 l_to2 =
      ControlFlowGraph.set_terminator cfg l_from @@ T_Branch (cond, a, b, l_to1, l_to2);
      ControlFlowGraph.connect cfg l_from l_to1;
      ControlFlowGraph.connect cfg l_from l_to2

    let allocate_block () = ControlFlowGraph.allocate_block cfg

    let i32_0 = Int32.of_int 0
    let i32_1 = Int32.of_int 1

    let add_instr_aux tag r lhs rhs = 
      match Hashtbl.find node2type tag with
      | TP_Int -> I_Add (r, lhs, rhs)
      | TP_Array _ -> I_Concat (r, lhs, rhs)
      | _ -> failwith "Typecheker error - '+' can only be applied to int or array"



    (* --------------------------------------------------- *)
    let rec translate_expression env current_bb = function
      | Ast.EXPR_Char {value; _} ->
        current_bb, E_Int (Int32.of_int @@ Char.code value)

      | Ast.EXPR_Id {id; _} ->
        current_bb, E_Reg (Environment.lookup_var id env)

      | Ast.EXPR_Int {value; _} ->
        current_bb, E_Int value

      | Ast.EXPR_Bool {value; _} ->
        if value = false
        then current_bb, E_Int i32_0
        else current_bb, E_Int i32_1

      | Ast.EXPR_String {value; _} -> 
        let r = allocate_register () in
        append_instruction current_bb @@
            I_NewArray (r, E_Int (Int32.of_int (String.length value)));
        String.iteri (fun i v -> 
            append_instruction current_bb 
            (I_StoreArray (E_Reg r, E_Int (Int32.of_int i), 
                E_Int (Int32.of_int @@ Char.code v)))) value;
        current_bb, E_Reg r

      | Ast.EXPR_Index {expr; index; _} ->
        let r = allocate_register () in
        let curr_bb, e1 = translate_expression env current_bb expr in
        let curr_bb, e2 = translate_expression env current_bb index in 
        append_instruction curr_bb (I_LoadArray (r, e1, e2));
        curr_bb, E_Reg r

      | Ast.EXPR_Length {arg; _} ->
        let r = allocate_register () in 
        let curr_bb, e_arg = translate_expression env current_bb arg in
        append_instruction curr_bb @@ I_Length (r, e_arg);
        curr_bb, E_Reg r

        (* ...duuuuuuuzo binopow... *)

      | Ast.EXPR_Binop {lhs; rhs; op=Ast.BINOP_Sub; _} ->
        let r = allocate_register () in
        let current_bb, res_lhs = translate_expression env current_bb lhs in
        let current_bb, res_rhs = translate_expression env current_bb rhs in
        append_instruction current_bb @@ I_Sub (r, res_lhs, res_rhs);
        current_bb, E_Reg r

      | Ast.EXPR_Binop {lhs; rhs; op=Ast.BINOP_Mult; _} ->
        let r = allocate_register () in
        let current_bb, res_lhs = translate_expression env current_bb lhs in
        let current_bb, res_rhs = translate_expression env current_bb rhs in
        append_instruction current_bb @@ I_Mul (r, res_lhs, res_rhs);
        current_bb, E_Reg r

      | Ast.EXPR_Binop {lhs; rhs; op=Ast.BINOP_Div; _} ->
        let r = allocate_register () in
        let current_bb, res_lhs = translate_expression env current_bb lhs in
        let current_bb, res_rhs = translate_expression env current_bb rhs in
        append_instruction current_bb @@ I_Div (r, res_lhs, res_rhs);
        current_bb, E_Reg r

      | Ast.EXPR_Binop {lhs; rhs; op=Ast.BINOP_Rem; _} ->
        let r = allocate_register () in
        let current_bb, res_lhs = translate_expression env current_bb lhs in
        let current_bb, res_rhs = translate_expression env current_bb rhs in
        append_instruction current_bb @@ I_Rem (r, res_lhs, res_rhs);
        current_bb, E_Reg r

      | Ast.EXPR_Binop {lhs; rhs; op=Ast.BINOP_Add; tag; _} ->
        let r = allocate_register () in
        let current_bb, res_lhs = translate_expression env current_bb lhs in
        let current_bb, res_rhs = translate_expression env current_bb rhs in
        append_instruction current_bb @@ add_instr_aux tag r res_lhs res_rhs;
        current_bb, E_Reg r

      | Ast.EXPR_Binop {lhs; rhs; op=(Ast.BINOP_Or | Ast.BINOP_And); _} as e ->
        let r = allocate_register () in
        let false_bb = allocate_block () in 
        let true_bb = translate_condition env current_bb false_bb e in
        let merge_bb = allocate_block () in
        append_instruction false_bb @@ I_Move (r, E_Int i32_0);
        append_instruction true_bb @@ I_Move (r, E_Int i32_1);
        set_jump true_bb merge_bb;
        set_jump false_bb merge_bb;
        merge_bb, E_Reg r

        (* koniec binopow chyba *)

      | Ast.EXPR_Unop {op=Ast.UNOP_Not; sub; _} ->
        let r = allocate_register () in
        let current_bb, e = translate_expression env current_bb sub in
        append_instruction current_bb @@ I_Not (r, e);
        current_bb, E_Reg r

      | Ast.EXPR_Unop {op=Ast.UNOP_Neg; sub; _} ->
        let r = allocate_register () in
        let current_bb, e = translate_expression env current_bb sub in
        append_instruction current_bb @@ I_Neg (r, e);
        current_bb, E_Reg r

        (* EXPR_Relation *)
        (* |  to wszystko jest zle :< *)
        (* v  jak napiszemy poprawnie AND i OR w translate_condition to do poprawki *)

      | Ast.EXPR_Relation {op=Ast.RELOP_Eq; lhs; rhs; _} ->
        let r = allocate_register () in
        let curr_bb, e1 = translate_expression env current_bb lhs in
        let curr_bb, e2 = translate_expression env current_bb rhs in
        append_instruction curr_bb @@ I_Set (r, COND_Eq,  e1, e2);
        curr_bb, E_Reg r

      | Ast.EXPR_Relation {op=Ast.RELOP_Ne; lhs; rhs; _} ->
        let r = allocate_register () in
        let curr_bb, e1 = translate_expression env current_bb lhs in
        let curr_bb, e2 = translate_expression env current_bb rhs in
        append_instruction curr_bb @@ I_Set (r, COND_Ne,  e1, e2);
        curr_bb, E_Reg r

      | Ast.EXPR_Relation {op=Ast.RELOP_Lt; lhs; rhs; _} ->
        let r = allocate_register () in
        let curr_bb, e1 = translate_expression env current_bb lhs in
        let curr_bb, e2 = translate_expression env current_bb rhs in
        append_instruction curr_bb @@ I_Set (r, COND_Lt,  e1, e2);
        curr_bb, E_Reg r

      | Ast.EXPR_Relation {op=Ast.RELOP_Gt; lhs; rhs; _} ->
        let r = allocate_register () in
        let curr_bb, e1 = translate_expression env current_bb lhs in
        let curr_bb, e2 = translate_expression env current_bb rhs in
        append_instruction curr_bb @@ I_Set (r, COND_Gt,  e1, e2);
        curr_bb, E_Reg r

      | Ast.EXPR_Relation {op=Ast.RELOP_Le; lhs; rhs; _} ->
        let r = allocate_register () in
        let curr_bb, e1 = translate_expression env current_bb lhs in
        let curr_bb, e2 = translate_expression env current_bb rhs in
        append_instruction curr_bb @@ I_Set (r, COND_Le,  e1, e2);
        curr_bb, E_Reg r

      | Ast.EXPR_Relation {op=Ast.RELOP_Ge; lhs; rhs; _} ->
        let r = allocate_register () in
        let curr_bb, e1 = translate_expression env current_bb lhs in
        let curr_bb, e2 = translate_expression env current_bb rhs in
        append_instruction curr_bb @@ I_Set (r, COND_Ge,  e1, e2);
        curr_bb, E_Reg r

      (* kooniec EXPR_Relation *)

      | Ast.EXPR_Call Call {callee; arguments; _} -> 
        let p = Environment.lookup_proc callee env in
        let aux (bb, l) expr = 
          let new_bb, e = translate_expression env bb expr 
          in new_bb, e::l 
        in let current_bb, xs = List.fold_left aux (current_bb, []) arguments in
        let rs = allocate_register () in
        append_instruction current_bb @@ I_Call ([rs], p, List.rev xs, []);
        current_bb, E_Reg rs


      | Ast.EXPR_Struct {elements; _} -> 
        let r = allocate_register () in
        append_instruction current_bb @@ I_NewArray (r, E_Int (Int32.of_int (List.length elements)));
        let aux (bb, l) expr = 
          let new_bb, e = translate_expression env bb expr 
          in new_bb, e::l
        in let current_bb, expr_list = List.fold_left aux (current_bb, []) elements in
        List.iteri (fun i e -> 
            append_instruction current_bb @@
            I_StoreArray (E_Reg r, E_Int (Int32.of_int i), e)) (List.rev expr_list);
        current_bb, E_Reg r

  (*   and translate_expr_list (bb, l) expr = 
      let new_bb, e = translate_expression env bb expr 
      in new_bb, e::l *)


    and translate_lvalue env current_bb e_reg = function
      | Ast.LVALUE_Id {id; _} -> 
        let r = E_Reg (Environment.lookup_var id env) in
        append_instruction current_bb @@ I_StoreMem (r, E_Int i32_0, e_reg);
        env, current_bb

      | Ast.LVALUE_Index {sub; index; _} ->
        let current_bb, i = translate_expression env current_bb index in
        let current_bb, xs = translate_expression env current_bb sub in
        append_instruction current_bb @@ I_StoreArray (xs, i, e_reg);
        env, current_bb

    (* --------------------------------------------------- *)
    and translate_condition env current_bb else_bb = function 
      | Ast.EXPR_Bool {value=true; _} ->
        current_bb

      | Ast.EXPR_Bool {value=false; _} ->
        set_jump current_bb else_bb;
        allocate_block ()

      (* Zaimplementuj dodatkowe przypadki *)

      | Ast.EXPR_Binop {lhs; rhs; op=Ast.BINOP_Or; _} ->
        let curr_bb, res_lhs = translate_expression env current_bb lhs in
        let next_bb = allocate_block () in
        let not_yet_bb = allocate_block () in
        set_branch COND_Ne res_lhs (E_Int i32_0) curr_bb next_bb not_yet_bb;
        let not_yet_bb, res_rhs = translate_expression env not_yet_bb rhs in
        set_branch COND_Ne res_rhs (E_Int i32_0) not_yet_bb next_bb else_bb;
        next_bb 

      | Ast.EXPR_Binop {lhs; rhs; op=Ast.BINOP_And; _} ->
        let curr_bb, res_lhs = translate_expression env current_bb lhs in
        let next_bb = allocate_block () in
        let not_yet_bb = allocate_block () in
        set_branch COND_Ne res_lhs (E_Int i32_0) curr_bb not_yet_bb else_bb;
        let not_yet_bb, res_rhs = translate_expression env not_yet_bb rhs in
        set_branch COND_Ne res_rhs (E_Int i32_0) not_yet_bb next_bb else_bb;
        next_bb 

      | e ->
        let current_bb, res = translate_expression env current_bb e in
        let next_bb = allocate_block () in 
        set_branch COND_Ne res (E_Int i32_0) current_bb next_bb else_bb;
        next_bb


    (* --------------------------------------------------- *)

    let rec translate_statement env current_bb = function

      | Ast.STMT_Return {values; _} ->
        let aux (bb, l) expr = 
          let new_bb, e = translate_expression env bb expr 
          in new_bb, e::l
        in let current_bb, expr_list = List.fold_left aux (current_bb, []) values in
        set_return current_bb expr_list;
        env, current_bb

      | Ast.STMT_Block stmt_block ->
        translate_block env current_bb stmt_block

      | Ast.STMT_If {cond; then_branch; else_branch; _} ->
        let else_bb = allocate_block () in
        let current_bb = translate_condition env current_bb else_bb cond in
        let env, current_bb = translate_statement env current_bb then_branch in
        let merge_bb = allocate_block () in
        (* czy mam tu dodawac jakies instrukcje??? *)
        set_jump current_bb merge_bb;
        begin match else_branch with
          | None -> 
            set_jump else_bb merge_bb; 
            env, merge_bb (* tu tez jest jakis problem z tym env :c 
            W sensie ze jesli cond=false to nie powinnam zwracac env zmienionego przez then_branch O.o *)

          | Some else_branch ->
            let env, else_bb = translate_statement env else_bb else_branch in
            set_jump else_bb merge_bb;
            env, merge_bb
        end

      | Ast.STMT_While {cond; body; _} as stmt_while -> 
        let false_bb = allocate_block () in
        let current_bb = translate_condition env current_bb false_bb cond in
        let env, current_bb = translate_statement env current_bb body in 
        let env, current_bb = translate_statement env current_bb stmt_while in
        let merge_bb = allocate_block () in
        set_jump current_bb merge_bb;
        set_jump false_bb merge_bb;
        env, merge_bb (*testy nie przechodza, czyli jest zleeee*)

      | Ast.STMT_Call Call {callee; arguments; _} ->
        let p = Environment.lookup_proc callee env in
        let aux (bb, l) expr = 
          let new_bb, e = translate_expression env bb expr 
          in new_bb, e::l 
        in let current_bb, xs = List.fold_left aux (current_bb, []) arguments in
        append_instruction current_bb @@ I_Call ([], p, List.rev xs, []);
        env, current_bb

      | Ast.STMT_Assign {lhs; rhs; _} ->
        let current_bb, res_rhs = translate_expression env current_bb rhs in
        translate_lvalue env current_bb res_rhs lhs  

      | Ast.STMT_VarDecl {var; init; _} ->
        let id = Ast.identifier_of_var_declaration var in
        let tp = Ast.type_expression_of_var_declaration var in
        begin match tp with
        | Ast.TEXPR_Int _
        
        | Ast.TEXPR_Bool _ ->
          let r = allocate_register () in
          let env = Environment.add_var id r env in
          begin match init with
          | None -> env, current_bb

          | Some e -> 
            let current_bb, res_init = translate_expression env current_bb e in
            append_instruction current_bb @@ I_Move (r, res_init);
            env, current_bb
          end

        | Ast.TEXPR_Array {sub; dim; _} -> failwith "not yet implemented"
          

        end


      | _ ->
        failwith "not yet implemented"


    and translate_block env current_bb (Ast.STMTBlock {body; _}) =
      List.fold_left (fun (env, bb) st -> translate_statement env bb st) 
        (env, current_bb) body

    let bind_var_declaration env vardecl =
      let r = allocate_register () in
      let env = Environment.add_var (Ast.identifier_of_var_declaration vardecl) r env in
      env, r

    let bind_formal_parameters env xs =
      let f env x = fst (bind_var_declaration env x) in 
      List.fold_left f env xs

  let translate_global_definition env = function
    | Ast.GDECL_Function {id; body=Some body; formal_parameters;_} ->
      let procid = Environment.lookup_proc id env in 
      let frame_size = 0 in
      let env = bind_formal_parameters env formal_parameters in
      let formal_parameters = List.length formal_parameters in
      let proc = Procedure {procid; cfg; frame_size; allocate_register; formal_parameters} in
      let first_bb = allocate_block () in
      let _, last_bb = translate_block env first_bb body in 
      ControlFlowGraph.connect cfg  last_bb (ControlFlowGraph.exit_label cfg);
      ControlFlowGraph.connect cfg  (ControlFlowGraph.entry_label cfg) first_bb;
      [proc]
    
    | _ ->
      []

  end

  let make_allocate_register () = 
    let counter = ref 0 in
    fun () ->
      let i = !counter in
      incr counter;
      REG_Tmp i


    let translate_global_definition node2type env gdef = 
      let cfg = ControlFlowGraph.create () in
      let module T = Translator(struct
        let cfg = cfg
        let node2type = node2type
        let allocate_register = make_allocate_register ()
      end) in
      T.translate_global_definition env gdef

    let translate_module node2type env (Ast.ModuleDefinition {global_declarations; _}) =
      List.flatten @@ List.map (translate_global_definition node2type env) global_declarations

    let translate_module mdef node2type =
      let env = Environment.empty in
      let env, symbols = Scanner.scan_module env mdef in
      let procedures = translate_module node2type env mdef in
      Program {procedures; symbols}
  end
