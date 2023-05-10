open Asttypes
open Parsetree
open Extensions_parsing

(******************************************************************************)
(** Individual language extension modules *)

(* Note [Check for immutable extension in comprehensions code]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   When we spot a comprehension for an immutable array, we need to make sure
   that both [comprehensions] and [immutable_arrays] are enabled.  But our
   general mechanism for checking for enabled extensions (in [of_ast]) won't
   work well here: it triggers when converting from
   e.g. [[%extensions.comprehensions.array] ...]  to the comprehensions-specific
   AST. But if we spot a [[%extensions.comprehensions.immutable]], there is no
   expression to translate.  So we just check for the immutable arrays extension
   when processing a comprehension expression for an immutable array.

   Note [Wrapping with make_entire_extension]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The topmost node in the encoded AST must always look like e.g.
   [%extension.comprehensions]. This allows the decoding machinery to know
   what extension is being used and what function to call to do the decoding.
   Accordingly, during encoding, after doing the hard work of converting the
   extension syntax tree into e.g. Parsetree.expression, we need to make a final
   step of wrapping the result in an [%extension.xyz] node. Ideally, this step
   would be done by part of our general structure, like we separate [of_ast]
   and [of_ast_internal] in the decode structure; this design would make it
   structurally impossible/hard to forget taking this final step.

   However, the final step is only one line of code (a call to
   [make_entire_extension]), but yet the name of the extension varies, as does
   the type of the payload. It would thus take several lines of code to execute
   this command otherwise, along with dozens of lines to create the structure in
   the first place. And so instead we just manually call [make_entire_extension]
   and refer to this Note as a reminder to authors of future extensions to
   remember to do this wrapping.
*)

(** List and array comprehensions *)
module Comprehensions = struct
  let extension_string = Language_extension.to_string Comprehensions

  type iterator =
    | Range of { start     : expression
               ; stop      : expression
               ; direction : direction_flag }
    | In of expression

  type clause_binding =
    { pattern    : pattern
    ; iterator   : iterator
    ; attributes : attribute list }

  type clause =
    | For of clause_binding list
    | When of expression

  type comprehension =
    { body    : expression
    ; clauses : clause list
    }

  type expression =
    | Cexp_list_comprehension  of comprehension
    | Cexp_array_comprehension of mutable_flag * comprehension

  (* The desugared-to-OCaml version of comprehensions is described by the
     following BNF, where [{% '...' | expr %}] refers to the result of
     [Expression.make_extension] (via [comprehension_expr]) as described at the
     top of [extensions_parsing.mli].

     {v
         comprehension ::=
           | {% 'comprehension.list' | '[' clauses ']' %}
           | {% 'comprehension.array' | '[|' clauses '|]' %}

         clauses ::=
           | {% 'comprehension.for' | 'let' iterator+ 'in' clauses %}
           | {% 'comprehension.when' | expr ';' clauses %}
           | {% 'comprehension.body' | expr %}

         iterator ::=
           | pattern '=' {% 'comprehension.for.range.upto' | expr ',' expr %}
           | pattern '=' {% 'comprehension.for.range.downto' | expr ',' expr %}
           | pattern '=' {% 'comprehension.for.in' | expr %}
     v}
  *)

  let comprehension_expr names x =
    Expression.wrap_desc ~attrs:[] @@
    Expression.make_extension (extension_string :: names) x

  (** First, we define how to go from the nice AST to the OCaml AST; this is
      the [expr_of_...] family of expressions, culminating in
      [expr_of_comprehension_expr]. *)

  let expr_of_iterator = function
    | Range { start; stop; direction } ->
        comprehension_expr
          [ "for"
          ; "range"
          ; match direction with
            | Upto   -> "upto"
            | Downto -> "downto" ]
          (Ast_helper.Exp.tuple [start; stop])
    | In seq ->
        comprehension_expr ["for"; "in"] seq

  let expr_of_clause_binding { pattern; iterator; attributes } =
    Ast_helper.Vb.mk ~attrs:attributes pattern (expr_of_iterator iterator)

  let expr_of_clause clause rest = match clause with
    | For iterators ->
        comprehension_expr
          ["for"]
          (Ast_helper.Exp.let_
             Nonrecursive (List.map expr_of_clause_binding iterators)
             rest)
    | When cond ->
        comprehension_expr ["when"] (Ast_helper.Exp.sequence cond rest)

  let expr_of_comprehension ~type_ { body; clauses } =
    comprehension_expr
      type_
      (List.fold_right
         expr_of_clause
         clauses
         (comprehension_expr ["body"] body))

  let expr_of ~loc eexpr =
    (* See Note [Wrapping with make_entire_extension] *)
    Expression.make_entire_extension ~loc extension_string (fun () ->
      match eexpr with
      | Cexp_list_comprehension comp ->
          expr_of_comprehension ~type_:["list"] comp
      | Cexp_array_comprehension (amut, comp) ->
          expr_of_comprehension
            ~type_:[ "array"
                   ; match amut with
                     | Mutable   -> "mutable"
                     | Immutable -> "immutable"
                   ]
            comp)

  (** Then, we define how to go from the OCaml AST to the nice AST; this is
      the [..._of_expr] family of expressions, culminating in
      [comprehension_expr_of_expr]. *)

  module Desugaring_error = struct
    type error =
      | Non_comprehension_extension_point of Extension_node_name.t
      | Non_extension
      | Bad_comprehension_extension_point of string list
      | No_clauses

    let report_error ~loc = function
      | Non_comprehension_extension_point ext_name ->
          Location.errorf ~loc
            "Tried to desugar the non-comprehension extension point %a@ \
             as part of a comprehension expression"
            Extension_node_name.pp_quoted_name ext_name
      | Non_extension ->
          Location.errorf ~loc
            "Tried to desugar a non-extension expression@ \
             as part of a comprehension expression"
      | Bad_comprehension_extension_point subparts ->
          Location.errorf ~loc
            "Unknown, unexpected, or malformed@ \
             comprehension extension point %a"
            Extension_node_name.pp_quoted_name
            Extension_node_name.(extension_string :: subparts)
      | No_clauses ->
          Location.errorf ~loc
            "Tried to desugar a comprehension with no clauses"

    exception Error of Location.t * error

    let () =
      Location.register_error_of_exn
        (function
          | Error(loc, err) -> Some (report_error ~loc err)
          | _ -> None)

    let raise expr err = raise (Error(expr.pexp_loc, err))
  end

  let expand_comprehension_extension_expr expr =
    match Expression.match_extension expr with
    | Some (comprehensions :: names, expr)
      when String.equal comprehensions extension_string ->
        names, expr
    | Some (ext_name, _) ->
        Desugaring_error.raise expr (Non_comprehension_extension_point ext_name)
    | None ->
        Desugaring_error.raise expr Non_extension

  let iterator_of_expr expr =
    match expand_comprehension_extension_expr expr with
    | ["for"; "range"; "upto"],
      { pexp_desc = Pexp_tuple [start; stop]; _ } ->
        Range { start; stop; direction = Upto }
    | ["for"; "range"; "downto"],
      { pexp_desc = Pexp_tuple [start; stop]; _ } ->
        Range { start; stop; direction = Downto }
    | ["for"; "in"], seq ->
        In seq
    | bad, _ ->
        Desugaring_error.raise expr (Bad_comprehension_extension_point bad)

  let clause_binding_of_vb { pvb_pat; pvb_expr; pvb_attributes; pvb_loc = _ } =
    { pattern = pvb_pat
    ; iterator = iterator_of_expr pvb_expr
    ; attributes = pvb_attributes }

  let add_clause clause comp = { comp with clauses = clause :: comp.clauses }

  let rec raw_comprehension_of_expr expr =
    match expand_comprehension_extension_expr expr with
    | ["for"], { pexp_desc = Pexp_let(Nonrecursive, iterators, rest); _ } ->
        add_clause
          (For (List.map clause_binding_of_vb iterators))
          (raw_comprehension_of_expr rest)
    | ["when"], { pexp_desc = Pexp_sequence(cond, rest); _ } ->
        add_clause
          (When cond)
          (raw_comprehension_of_expr rest)
    | ["body"], body ->
        { body; clauses = [] }
    | bad, _ ->
        Desugaring_error.raise expr (Bad_comprehension_extension_point bad)

  let comprehension_of_expr expr =
    match raw_comprehension_of_expr expr with
    | { body = _; clauses = [] } ->
        Desugaring_error.raise expr No_clauses
    | comp -> comp

  let comprehension_expr_of_expr expr =
    match expand_comprehension_extension_expr expr with
    | ["list"], comp ->
        Cexp_list_comprehension (comprehension_of_expr comp)
    | ["array"; "mutable"], comp ->
        Cexp_array_comprehension (Mutable, comprehension_of_expr comp)
    | ["array"; "immutable"], comp ->
        (* assert_extension_enabled:
           See Note [Check for immutable extension in comprehensions code] *)
        assert_extension_enabled ~loc:expr.pexp_loc Immutable_arrays;
        Cexp_array_comprehension (Immutable, comprehension_of_expr comp)
    | bad, _ ->
        Desugaring_error.raise expr (Bad_comprehension_extension_point bad)
end

module N_ary_function = struct
  let extension_string = Language_extension.to_string Syntactic_function_arity

  type function_body =
    | Pfunction_body of expression
    | Pfunction_cases of case list * Location.t * attributes

  type function_param =
    | Pparam_val of arg_label * expression option * pattern
    (** [Pparam_val (lbl, exp0, P)] represents the parameter:
        - [P]
          when [lbl] is {{!Asttypes.arg_label.Nolabel}[Nolabel]}
          and [exp0] is [None]
        - [~l:P]
          when [lbl] is {{!Asttypes.arg_label.Labelled}[Labelled l]}
          and [exp0] is [None]
        - [?l:P]
          when [lbl] is {{!Asttypes.arg_label.Optional}[Optional l]}
          and [exp0] is [None]
        - [?l:(P = E0)]
          when [lbl] is {{!Asttypes.arg_label.Optional}[Optional l]}
          and [exp0] is [Some E0]

        Note: If [E0] is provided, only
        {{!Asttypes.arg_label.Optional}[Optional]} is allowed.
    *)
    | Pparam_newtype of string loc * Location.t
    (** [Pparam_newtype (x, loc)] represents the parameter [(type x)].
        [x] carries the location of the identifier, whereas [loc] is
        the location of the [(type x)] as a whole.

        Multiple parameters [(type a b c)] are represented as multiple
        [Pparam_newtype] nodes.
    *)

  type type_constraint =
    | Pconstraint of core_type
    | Pcoerce of core_type option * core_type

  type alloc_mode = Local | Global

  type function_constraint =
    { alloc_mode: alloc_mode;
      type_constraint: type_constraint;
    }

  type expression =
    function_param list * function_constraint option * function_body

  module Extension_node = struct
    type t =
      | End_cases
      | End_expression_body

    let to_extension_suffix = function
      | End_cases -> [ "end"; "cases" ]
      | End_expression_body -> [ "end"; "expression_body" ]

    let of_extension_suffix = function
      | [ "end"; "cases" ] -> Some End_cases
      | [ "end"; "expression_body" ] -> Some End_expression_body
      | _ -> None

    let format ppf t =
      Extension_node_name.pp_quoted_name
        ppf
        (extension_string :: to_extension_suffix t)
  end

  module Desugaring_error = struct
    type error =
      | Non_syntactic_arity_extension_point of Extension_node_name.t
      | Missing_closing_extension_point
      | Misannotated_function_cases
      | Bad_syntactic_arity_extension_point of string list
      | Unknown_attributes of attributes

    let report_error ~loc = function
      | Non_syntactic_arity_extension_point name ->
          Location.errorf ~loc
            "Tried to desugar the non-syntactic-arity extension point \
             %a as part of a syntactic-arity expression."
            Extension_node_name.pp_quoted_name name
      | Missing_closing_extension_point ->
          Location.errorf ~loc
            "Expected a syntactic-arity extension point delimiting the end of \
             the n-ary function before reaching a node of this kind. The only \
             legal construct is a nested sequence of Pexp_fun and Pexp_newtype \
             nodes, optionally followed by a Pexp_coerce or Pexp_constraint \
             node, ending in %a or %a."
            Extension_node.format Extension_node.End_cases
            Extension_node.format Extension_node.End_expression_body
      | Misannotated_function_cases ->
          Location.errorf ~loc
            "%a may be applied only to a function expression."
            Extension_node.format Extension_node.End_cases
      | Bad_syntactic_arity_extension_point suffix ->
          Location.errorf ~loc
            "Unknown syntactic-arity extension point %a."
            Extension_node_name.pp_quoted_name
            Extension_node_name.(extension_string :: suffix)
      | Unknown_attributes attrs ->
          Location.errorf ~loc
            "Unknown syntactic-arity attribute set %s."
            (String.concat "," (List.map (fun a -> a.attr_name.txt) attrs))

    exception Error of Location.t * error

    let () =
      Location.register_error_of_exn
        (function
          | Error(loc, err) -> Some (report_error ~loc err)
          | _ -> None)

    let raise expr err = raise (Error (expr.pexp_loc, err))
  end

  let expand_comprehension_extension_expr expr =
    match Expression.match_extension expr with
    | None -> None
    | Some (syntactic_arity :: suffix, expr)
      when String.equal syntactic_arity extension_string ->
        begin match Extension_node.of_extension_suffix suffix with
          | Some ext -> Some (ext, expr)
          | None ->
              Desugaring_error.raise
                expr
                (Bad_syntactic_arity_extension_point suffix)
        end
    | Some (name, _) ->
        Desugaring_error.raise
          expr
          (Non_syntactic_arity_extension_point name)

  let check_close expr ~rev_params ~function_constraint : expression option =
    match expand_comprehension_extension_expr expr with
    | None -> None
    | Some (End_cases, ({ pexp_desc = Pexp_function cases } as expr)) ->
        let { pexp_loc = loc; pexp_attributes = attrs } = expr in
        let params = List.rev rev_params in
        Some (params, function_constraint, Pfunction_cases (cases, loc, attrs))
    | Some (End_cases, expr) ->
        Desugaring_error.raise expr Misannotated_function_cases
    | Some (End_expression_body, expr) ->
        let params = List.rev rev_params in
        Some (params, function_constraint, Pfunction_body expr)

  let require_close expr ~rev_params ~type_constraint ~alloc_mode =
    match
      check_close expr ~rev_params
        ~function_constraint:(Some { type_constraint; alloc_mode })
    with
    | Some result -> result
    | None ->
        Desugaring_error.raise expr Missing_closing_extension_point

  let rec create_n_ary_function expr ~rev_params =
    match check_close expr ~function_constraint:None ~rev_params with
    | Some result -> result
    | None ->
        let alloc_mode =
          match expr.pexp_attributes with
          | [ { attr_name = { txt = "local" } } ] -> Local
          | [] -> Global
          | attrs -> Desugaring_error.raise expr (Unknown_attributes attrs)
        in
        match expr.pexp_desc with
        | Pexp_fun (label, default, pat, body) ->
            let param = Pparam_val (label, default, pat) in
            create_n_ary_function body ~rev_params:(param :: rev_params)
        | Pexp_newtype (newtype, body) ->
            let loc = { newtype.loc with loc_ghost = true } in
            let param = Pparam_newtype (newtype, loc) in
            create_n_ary_function body ~rev_params:(param :: rev_params)
        | Pexp_constraint (body, ty) ->
            require_close body
              ~rev_params ~type_constraint:(Pconstraint ty) ~alloc_mode
        | Pexp_coerce (body, ty1, ty2) ->
            require_close body
              ~rev_params ~type_constraint:(Pcoerce (ty1, ty2)) ~alloc_mode
        | _ -> Desugaring_error.raise expr Missing_closing_extension_point

  let of_expr expr = create_n_ary_function expr ~rev_params:[]

  let n_ary_function_expr ext x =
    let suffix = Extension_node.to_extension_suffix ext in
    Expression.wrap_desc ~attrs:[] @@
    Expression.make_extension (extension_string :: suffix) x

  let expr_of ~loc (params, constraint_, body : expression) =
    (* See Note [Wrapping with make_entire_extension] *)
    Expression.make_entire_extension ~loc extension_string (fun () ->
      let body =
        match body with
        | Pfunction_body body ->
            n_ary_function_expr End_expression_body body
        | Pfunction_cases (cases, loc, attrs) ->
            n_ary_function_expr End_cases
              (Ast_helper.Exp.function_ cases ~loc ~attrs
                 [@alert "-deprecated"])
      in
      let constrained_body =
        let attrs ~alloc_mode =
          match alloc_mode with
          | Global -> None
          | Local ->
              Some [ Ast_helper.Attr.mk (Location.mknoloc "local") (PStr []) ]
        in
        match constraint_ with
        | None -> body
        | Some { alloc_mode; type_constraint = Pconstraint ty } ->
            let attrs = attrs ~alloc_mode in
            Ast_helper.Exp.constraint_ ?attrs body ty
        | Some { alloc_mode; type_constraint = Pcoerce (ty1, ty2) } ->
            let attrs = attrs ~alloc_mode in
            Ast_helper.Exp.coerce ?attrs body ty1 ty2
      in
      List.fold_right
        (fun param body ->
           match param with
           | Pparam_val (label, default, pat) ->
               (Ast_helper.Exp.fun_ label default pat body
                  [@alert "-deprecated"])
           | Pparam_newtype (newtype, loc) ->
               Ast_helper.Exp.newtype newtype body ~loc)
        params
        constrained_body)

end

(** Immutable arrays *)
module Immutable_arrays = struct
  type nonrec expression =
    | Iaexp_immutable_array of expression list

  type nonrec pattern =
    | Iapat_immutable_array of pattern list

  let extension_string = Language_extension.to_string Immutable_arrays

  let expr_of ~loc = function
    | Iaexp_immutable_array elts ->
      (* See Note [Wrapping with make_entire_extension] *)
      Expression.make_entire_extension ~loc extension_string (fun () ->
        Ast_helper.Exp.array elts)

  let of_expr expr = match expr.pexp_desc with
    | Pexp_array elts -> Iaexp_immutable_array elts
    | _ -> failwith "Malformed immutable array expression"

  let pat_of ~loc = function
    | Iapat_immutable_array elts ->
      (* See Note [Wrapping with make_entire_extension] *)
      Pattern.make_entire_extension ~loc extension_string (fun () ->
        Ast_helper.Pat.array elts)

  let of_pat expr = match expr.ppat_desc with
    | Ppat_array elts -> Iapat_immutable_array elts
    | _ -> failwith "Malformed immutable array pattern"
end

(** Module strengthening *)
module Strengthen = struct
  type nonrec module_type =
    { mty : Parsetree.module_type; mod_id : Longident.t Location.loc }

  let extension_string = Language_extension.to_string Module_strengthening

  (* Encoding: [S with M] becomes [functor (_ : S) -> (module M)], where
     the [(module M)] is a [Pmty_alias].  This isn't syntax we can write, but
     [(module M)] can be the inferred type for [M], so this should be fine. *)

  let mty_of ~loc { mty; mod_id } =
    (* See Note [Wrapping with make_entire_extension] *)
    Module_type.make_entire_extension ~loc extension_string (fun () ->
      Ast_helper.Mty.functor_ (Named (Location.mknoloc None, mty))
        (Ast_helper.Mty.alias mod_id))

  let of_mty mty = match mty.pmty_desc with
    | Pmty_functor(Named(_, mty), {pmty_desc = Pmty_alias mod_id}) ->
       { mty; mod_id }
    | _ -> failwith "Malformed strengthened module type"
end

(******************************************************************************)
(** The interface to language extensions, which we export *)

module type AST = sig
  type t
  type ast

  val of_ast : ast -> t option
end

module Expression = struct
  module M = struct
    module AST = Extensions_parsing.Expression

    type t =
      | Eexp_comprehension   of Comprehensions.expression
      | Eexp_immutable_array of Immutable_arrays.expression
      | Eexp_n_ary_function  of N_ary_function.expression

    let of_ast_internal (ext : Language_extension.t) expr = match ext with
      | Comprehensions ->
        Some (Eexp_comprehension (Comprehensions.comprehension_expr_of_expr expr))
      | Immutable_arrays ->
        Some (Eexp_immutable_array (Immutable_arrays.of_expr expr))
      | Syntactic_function_arity ->
        Some (Eexp_n_ary_function (N_ary_function.of_expr expr))
      | _ -> None
  end

  include M
  include Make_of_ast(M)

  let expr_of ~loc t =
    match t with
    | Eexp_comprehension   c -> Comprehensions.expr_of   ~loc c
    | Eexp_immutable_array i -> Immutable_arrays.expr_of ~loc i
    | Eexp_n_ary_function  n -> N_ary_function.expr_of   ~loc n
end

module Pattern = struct
  module M = struct
    module AST = Extensions_parsing.Pattern

    type t =
      | Epat_immutable_array of Immutable_arrays.pattern

    let of_ast_internal (ext : Language_extension.t) pat = match ext with
      | Immutable_arrays ->
        Some (Epat_immutable_array (Immutable_arrays.of_pat pat))
      | _ -> None
  end

  include M
  include Make_of_ast(M)
end

module Module_type = struct
  module M = struct
    module AST = Extensions_parsing.Module_type

    type t =
      | Emty_strengthen of Strengthen.module_type

    let of_ast_internal (ext : Language_extension.t) mty = match ext with
      | Module_strengthening ->
        Some (Emty_strengthen (Strengthen.of_mty mty))
      | _ -> None
  end

  include M
  include Make_of_ast(M)
end
