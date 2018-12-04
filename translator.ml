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

    let add_instr tag r lhs rhs = 
      match Hashtbl.find node2type tag with
      | TP_Int -> I_Add (r, lhs, rhs)
      | TP_Array _ -> I_Concat (r, lhs, rhs)
      | _ -> failwith "Typecheker error - '+' only applied to int or array"

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
        append_instruction current_bb 
            (I_NewArray (r, E_Int (Int32.of_int (String.length value))));
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
        append_instruction current_bb @@ add_instr tag r res_lhs res_rhs;
        current_bb, E_Reg r

      | Ast.EXPR_Binop {lhs; rhs; op=(Ast.BINOP_Or | Ast.BINOP_And); _} as e ->
        let r = allocate_register () in
        let bb_false = allocate_block () in 
        let bb_true = translate_condition env current_bb bb_false e in
        let bb_merge = allocate_block () in
        append_instruction bb_false @@ I_Move (r, E_Int i32_0);
        append_instruction bb_true @@ I_Move (r, E_Int i32_1);
        set_jump bb_true bb_merge;
        set_jump bb_false bb_merge;
        bb_merge, E_Reg r


        (* Czy ten or i and maja tak tez wygladac? *)
        (* i teraz cos z add madrego trzeba  *)





      | _ ->
        failwith "not yet implemented"

    (* --------------------------------------------------- *)
    and translate_condition env current_bb else_bb = function 
      | Ast.EXPR_Bool {value=true; _} ->
        current_bb

      | Ast.EXPR_Bool {value=false; _} ->
        set_jump current_bb else_bb;
        allocate_block ()

      (* Zaimplementuj dodatkowe przypadki *)

      (*to chcemy dla OR i AND zrobic na pewno*)
      (* | Ast.EXPR_Binop {lhs; rhs; op=Ast.BINOP_Or; _} *)

      | e ->
        let current_bb, res = translate_expression env current_bb e in
        let next_bb = allocate_block () in 
        set_branch COND_Ne res (E_Int i32_0) current_bb next_bb else_bb;
        next_bb


    (* --------------------------------------------------- *)

    let rec translate_statement env current_bb = function
      | _ ->
        failwith "not yet implemented"


    and translate_block env current_bb (Ast.STMTBlock {body; _}) =
      failwith "not yet implemented"

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
