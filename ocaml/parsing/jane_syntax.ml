open Asttypes
open Parsetree
open Jane_syntax_parsing

(******************************************************************************)
(** Individual language extension modules *)

(* Note [Check for immutable extension in comprehensions code]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   When we spot a comprehension for an immutable array, we need to make sure
   that both [comprehensions] and [immutable_arrays] are enabled.  But our
   general mechanism for checking for enabled extensions (in [of_ast]) won't
   work well here: it triggers when converting from
   e.g. [[%jane.non_erasable.comprehensions.array] ...] to the
   comprehensions-specific AST. But if we spot a
   [[%jane.non_erasable.comprehensions.immutable]], there is no expression to
   translate. So we just check for the immutable arrays extension when
   processing a comprehension expression for an immutable array.

   Note [Wrapping with make_entire_jane_syntax]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The topmost node in the encoded AST must always look like e.g.
   [%jane.non_erasable.comprehensions]. (More generally,
   [%jane.ERASABILITY.FEATURE] or [@jane.ERASABILITY.FEATURE].) This allows the
   decoding machinery to know what extension is being used and what function to
   call to do the decoding. Accordingly, during encoding, after doing the hard
   work of converting the extension syntax tree into e.g. Parsetree.expression,
   we need to make a final step of wrapping the result in a [%jane.*.xyz] node.
   Ideally, this step would be done by part of our general structure, like we
   separate [of_ast] and [of_ast_internal] in the decode structure; this design
   would make it structurally impossible/hard to forget taking this final step.

   However, the final step is only one line of code (a call to
   [make_entire_jane_syntax]), but yet the name of the feature varies, as does
   the type of the payload. It would thus take several lines of code to execute
   this command otherwise, along with dozens of lines to create the structure in
   the first place. And so instead we just manually call
   [make_entire_jane_syntax] and refer to this Note as a reminder to authors of
   future syntax features to remember to do this wrapping.

   Note [Outer attributes at end]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   The order of attributes matters for several reasons:
   - If the user writes attributes on a Jane Street OCaml construct, where
     should those appear with respect to the Jane Syntax attribute that
     introduces the construct?
   - Some Jane Syntax embeddings use attributes, and sometimes an AST node will
     have multiple Jane Syntax-related attributes on it. Which attribute should
     Jane Syntax interpret first?

   Both of these questions are settled by a convention where attributes
   appearing later in an attribute list are considered to be "outer" to
   attributes appearing earlier. (ppxlib adopted this convention, and thus we
   need to as well for compatibility.)

   - User-written attributes appear later in the attribute list than
     a Jane Syntax attribute that introduces a syntactic construct.
   - If multiple Jane Syntax attributes appear on an AST node, the ones
     appearing later in the attribute list should be interpreted first.
*)

(** List and array comprehensions *)
module Comprehensions = struct
  let feature : Feature.t = Language_extension Comprehensions
  let extension_string = Feature.extension_component feature

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
     [Expression.make_jane_syntax] (via [comprehension_expr]) as described at
     the top of [jane_syntax_parsing.mli].

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

  let comprehension_expr names x = Expression.make_jane_syntax feature names x

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
    (* We elect to wrap the body in a new AST node (here, [Pexp_lazy])
       because it makes it so there is no AST node that can carry multiple Jane
       Syntax-related attributes in addition to user-written attributes. This
       choice simplifies the definition of [comprehension_expr_of_expr], as
       part of its contract is threading through the user-written attributes
       on the outermost node.
    *)
    comprehension_expr
      type_
      (Ast_helper.Exp.lazy_
        (List.fold_right
          expr_of_clause
          clauses
          (comprehension_expr ["body"] body)))

  let expr_of ~loc cexpr =
    (* See Note [Wrapping with make_entire_jane_syntax] *)
    Expression.make_entire_jane_syntax ~loc feature (fun () ->
      match cexpr with
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
      | Non_comprehension_embedding of Embedded_name.t
      | Non_embedding
      | Bad_comprehension_embedding of string list
      | No_clauses

    let report_error ~loc = function
      | Non_comprehension_embedding name ->
          Location.errorf ~loc
            "Tried to desugar the non-comprehension embedded term %a@ \
             as part of a comprehension expression"
            Embedded_name.pp_quoted_name name
      | Non_embedding ->
          Location.errorf ~loc
            "Tried to desugar a non-embedded expression@ \
             as part of a comprehension expression"
      | Bad_comprehension_embedding subparts ->
          Location.errorf ~loc
            "Unknown, unexpected, or malformed@ comprehension embedded term %a"
            Embedded_name.pp_quoted_name
            (Embedded_name.of_feature feature subparts)
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

  (* Returns the expression node with the outermost Jane Syntax-related
     attribute removed. *)
  let expand_comprehension_extension_expr expr =
    match find_and_remove_jane_syntax_attribute expr.pexp_attributes with
    | Some (ext_name, attributes) -> begin
        match Jane_syntax_parsing.Embedded_name.components ext_name with
        | comprehensions :: names
          when String.equal comprehensions extension_string ->
            names, { expr with pexp_attributes = attributes }
        | _ :: _ ->
            Desugaring_error.raise expr (Non_comprehension_embedding ext_name)
      end
    | None ->
        Desugaring_error.raise expr Non_embedding

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
        Desugaring_error.raise expr (Bad_comprehension_embedding bad)

  let clause_binding_of_vb { pvb_pat; pvb_expr; pvb_attributes; pvb_loc = _ } =
    { pattern = pvb_pat
    ; iterator = iterator_of_expr pvb_expr
    ; attributes = pvb_attributes }

  let add_clause clause comp = { comp with clauses = clause :: comp.clauses }

  let comprehension_of_expr =
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
          Desugaring_error.raise expr (Bad_comprehension_embedding bad)
    in
    fun expr ->
      match raw_comprehension_of_expr expr with
      | { body = _; clauses = [] } ->
          Desugaring_error.raise expr No_clauses
      | comp -> comp

  (* Returns remaining unconsumed attributes on outermost expression *)
  let comprehension_expr_of_expr expr =
    let name, wrapper = expand_comprehension_extension_expr expr in
    let comp =
      match name, wrapper.pexp_desc with
      | ["list"], Pexp_lazy comp ->
          Cexp_list_comprehension (comprehension_of_expr comp)
      | ["array"; "mutable"], Pexp_lazy comp ->
          Cexp_array_comprehension (Mutable, comprehension_of_expr comp)
      | ["array"; "immutable"], Pexp_lazy comp ->
          (* assert_extension_enabled:
            See Note [Check for immutable extension in comprehensions code] *)
          assert_extension_enabled ~loc:expr.pexp_loc Immutable_arrays ();
          Cexp_array_comprehension (Immutable, comprehension_of_expr comp)
      | bad, _ ->
          Desugaring_error.raise expr (Bad_comprehension_embedding bad)
    in
    comp, wrapper.pexp_attributes
end

(** Immutable arrays *)
module Immutable_arrays = struct
  type nonrec expression =
    | Iaexp_immutable_array of expression list

  type nonrec pattern =
    | Iapat_immutable_array of pattern list

  let feature : Feature.t = Language_extension Immutable_arrays

  let expr_of ~loc = function
    | Iaexp_immutable_array elts ->
      (* See Note [Wrapping with make_entire_jane_syntax] *)
      Expression.make_entire_jane_syntax ~loc feature (fun () ->
        Ast_helper.Exp.array elts)

  (* Returns remaining unconsumed attributes *)
  let of_expr expr = match expr.pexp_desc with
    | Pexp_array elts -> Iaexp_immutable_array elts, expr.pexp_attributes
    | _ -> failwith "Malformed immutable array expression"

  let pat_of ~loc = function
    | Iapat_immutable_array elts ->
      (* See Note [Wrapping with make_entire_jane_syntax] *)
      Pattern.make_entire_jane_syntax ~loc feature (fun () ->
        Ast_helper.Pat.array elts)

  (* Returns remaining unconsumed attributes *)
  let of_pat pat = match pat.ppat_desc with
    | Ppat_array elts -> Iapat_immutable_array elts, pat.ppat_attributes
    | _ -> failwith "Malformed immutable array pattern"
end

module N_ary_functions = struct
  let feature : Feature.t = Builtin
  let extension_string = Feature.extension_component feature

  type function_body =
    | Pfunction_body of expression
    | Pfunction_cases of case list * Location.t * attributes

  type function_param =
    | Pparam_val of arg_label * expression option * pattern
    | Pparam_newtype of string loc * Location.t

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

  (** An attribute of the form [@jane.erasable._builtin.*] that's relevant
      to n-ary functions. The "*" in the example is what we call the "suffix".
      See the below BNF for the meaning of the attributes.
  *)
  module Attribute_node = struct
    type after_fun =
      | Cases
      | Constraint_then_cases

    type t =
      | Top_level
      | Fun_then of after_fun
      | Local_constraint

    let to_suffix = function
      | Top_level -> []
      | Fun_then Cases -> [ "cases" ]
      | Fun_then Constraint_then_cases -> [ "constraint"; "cases" ]
      | Local_constraint -> [ "local_constraint" ]

    let of_suffix = function
      | [] -> Some Top_level
      | [ "cases" ] -> Some (Fun_then Cases)
      | [ "constraint"; "cases" ] -> Some (Fun_then Constraint_then_cases)
      | [ "local_constraint" ] -> Some Local_constraint
      | _ -> None

    let format ppf t =
      Embedded_name.pp_quoted_name
        ppf
        (Embedded_name.of_feature feature (to_suffix t))
  end

  module Desugaring_error = struct
    type error =
      | Bad_syntactic_arity_embedding of string list
      | Expected_constraint_or_coerce
      | Expected_function_cases of Attribute_node.t
      | Expected_fun_or_newtype of Attribute_node.t
      | Parameterless_function

    let report_error ~loc = function
      | Bad_syntactic_arity_embedding suffix ->
          Location.errorf ~loc
            "Unknown syntactic-arity extension point %a."
            Embedded_name.pp_quoted_name
            (Embedded_name.of_feature feature suffix)
      | Expected_constraint_or_coerce ->
          Location.errorf ~loc
            "Expected a Pexp_constraint or Pexp_coerce node at this position."
      | Expected_function_cases attribute ->
          Location.errorf ~loc
            "Expected a Pexp_function node in this position, as the enclosing \
             Pexp_fun is annotated with %a."
            Attribute_node.format attribute
      | Expected_fun_or_newtype attribute ->
          Location.errorf ~loc
            "Only Pexp_fun or Pexp_newtype may carry the attribute %a."
            Attribute_node.format attribute
      | Parameterless_function ->
          Location.errorf ~loc
            "The expression is a Jane Syntax encoding of a function with no \
             parameters, which is an invalid expression."

    exception Error of Location.t * error

    let () =
      Location.register_error_of_exn
        (function
          | Error(loc, err) -> Some (report_error ~loc err)
          | _ -> None)

    let raise_with_loc loc err = raise (Error (loc, err))
    let raise expr err = raise (Error (expr.pexp_loc, err))
  end

  (* The desugared-to-OCaml version of an n-ary function is described by the
     following BNF, where [{% '...' | expr %}] refers to the result of
     [Expression.make_jane_syntax] (via n_ary_function_expr) as described at the
     top of [jane_syntax_parsing.mli]. Within the '...' string, I use <...>
     brackets to denote string interpolation.

     {v
         (* The entry point.

            The encoding only puts attributes on:
              - [fun] nodes
              - constraint/coercion nodes, on the rare occasions
                that a constraint should be interpreted at the [local] mode

            This ensures that we rarely put attributes on the *body* of the
            function, which means that ppxes that move or transform the body
            of a function won't make Jane Syntax complain.
         *)
         n_ary_function ::=
           | nested_n_ary_function
           (* A function need not have [fun] params; it can be a function
              or a constrained function. These need not have extra attributes,
              except in the rare case that the function is constrained at the
              local mode.
           *)
           | pexp_function
           | constraint_with_mode_then(pexp_function)

         nested_n_ary_function ::=
           | fun_then(nested_n_ary_function)
           | fun_then(constraint_with_mode_then(expression))
           | {% '_builtin.cases' | fun_then(pexp_function) }
           | {% '_builtin.constraint.cases' |
               fun_then(constraint_with_mode_then(pexp_function)) }
           | fun_then(expression)


         fun_then(body) ::=
           | 'fun' pattern '->' body (* Pexp_fun *)
           | 'fun' '(' 'type' ident ')' '->' body (* Pexp_newtype *)

         pexp_function ::=
           | 'function' cases

         constraint_then(ast) ::=
           | ast (':' type)? ':>' type (* Pexp_coerce *)
           | ast ':' type              (* Pexp_constraint *)

         constraint_with_mode_then(ast) ::=
           | constraint_then(ast)
           | {% '_builtin.local_constraint' | constraint_then(ast) %}
     v}
  *)

  let expand_n_ary_expr expr =
    match find_and_remove_jane_syntax_attribute expr.pexp_attributes with
    | None -> None
    | Some (ext_name, attributes) -> begin
        match Jane_syntax_parsing.Embedded_name.components ext_name with
        | feature :: suffix
          when String.equal feature extension_string -> begin
            match Attribute_node.of_suffix suffix with
            | Some ext -> Some (ext, attributes)
            | None ->
              Desugaring_error.raise
                expr
                (Bad_syntactic_arity_embedding suffix)
          end
        | _ :: _ -> None
      end

  let require_function_cases expr ~arity_attribute =
    match expr.pexp_desc with
    | Pexp_function cases -> cases
    | _ -> Desugaring_error.raise expr (Expected_function_cases arity_attribute)

  let constraint_alloc_mode expr : alloc_mode =
    match expand_n_ary_expr expr with
    | Some (Local_constraint, _) -> Local
    | _ -> Global

  let check_constraint expr =
    match expr.pexp_desc with
    | Pexp_constraint (e, ty) ->
        let alloc_mode = constraint_alloc_mode expr in
        Some ({ alloc_mode; type_constraint = Pconstraint ty }, e)
    | Pexp_coerce (e, ty1, ty2) ->
        let alloc_mode = constraint_alloc_mode expr in
        Some ({ alloc_mode; type_constraint = Pcoerce (ty1, ty2) }, e)
    | _ -> None

  let require_constraint expr =
    match check_constraint expr with
    | Some constraint_ -> constraint_
    | None -> Desugaring_error.raise expr Expected_constraint_or_coerce

  let check_param pexp_desc =
    match pexp_desc with
    | Pexp_fun (lbl, def, pat, body) ->
        Some (Pparam_val (lbl, def, pat), body)
    | Pexp_newtype (newtype, body) ->
        let loc = { newtype.loc with loc_ghost = true } in
        Some (Pparam_newtype (newtype, loc), body)
    | _ -> None

  let require_param pexp_desc pexp_loc ~arity_attribute =
    match check_param pexp_desc with
    | Some x -> x
    | None ->
        Desugaring_error.raise_with_loc pexp_loc
          (Expected_fun_or_newtype arity_attribute)

  (* Should only be called on [Pexp_fun] and [Pexp_newtype]. *)
  let extract_fun_params =
    let open struct
      type continue_or_stop =
        | Continue of Parsetree.expression
        | Stop of function_constraint option * function_body
    end
    in
    let extract_next_fun_param expr
        (* The attributes are the remaining unconsumed attributes on the
          Pexp_fun or Pexp_newtype node.
        *)
        : (function_param * attributes) option * continue_or_stop
      =
      match expand_n_ary_expr expr with
      | None -> begin
          match check_param expr.pexp_desc with
          | Some (param, body) ->
              Some (param, expr.pexp_attributes), Continue body
          | None ->
              None, Stop (None, Pfunction_body expr)
        end
      | Some (arity_attribute, unconsumed_attributes) -> begin
          match arity_attribute with
          | Top_level -> None, Stop (None, Pfunction_body expr)
          | Local_constraint ->
              (* We need not pass through any unconsumed attributes, as
                 [Local_constraint] isn't the outermost Jane Syntax node:
                 [extract_fun_params] took in [Pexp_fun] or [Pexp_newtype].
              *)
              let function_constraint, body = require_constraint expr in
              None, Stop (Some function_constraint, Pfunction_body body)
          | Fun_then after_fun ->
              let param, body =
                require_param expr.pexp_desc expr.pexp_loc ~arity_attribute
              in
              let continue_or_stop =
                match after_fun with
                | Cases ->
                    let cases = require_function_cases body ~arity_attribute in
                    let function_body =
                      Pfunction_cases
                        (cases, body.pexp_loc, body.pexp_attributes)
                    in
                    Stop (None, function_body)
                | Constraint_then_cases ->
                    let function_constraint, body = require_constraint body in
                    let cases = require_function_cases body ~arity_attribute in
                    let function_body =
                      Pfunction_cases
                        (cases, body.pexp_loc, body.pexp_attributes)
                    in
                    Stop (Some function_constraint, function_body)
              in
              Some (param, unconsumed_attributes), continue_or_stop
          end
    in
    let rec loop expr ~rev_params =
      let next_param, continue_or_stop = extract_next_fun_param expr in
      let rev_params =
        match next_param with
        | None -> rev_params
        | Some (x, _) -> x :: rev_params
      in
      match continue_or_stop with
      | Continue body -> loop body ~rev_params
      | Stop (function_constraint, body) ->
          let params = List.rev rev_params in
          params, function_constraint, body
    in
    fun expr ->
      begin match expr.pexp_desc with
        | Pexp_newtype _ | Pexp_fun _ -> ()
        | _ ->
            Misc.fatal_error "called on something that isn't a newtype or fun"
      end;
      let unconsumed_attributes =
        match extract_next_fun_param expr with
        | Some (_, attributes), _ -> attributes
        | None, _ -> Desugaring_error.raise expr Parameterless_function
      in
      loop expr ~rev_params:[], unconsumed_attributes

  (* Returns remaining unconsumed attributes on outermost expression *)
  let of_expr =
    let function_without_additional_params cases constraint_ loc : expression =
      (* If the outermost node is function cases, we place the
          attributes on the function node as a whole rather than on the
          [Pfunction_cases] body.
      *)
      [], constraint_, Pfunction_cases (cases, loc, [])
    in
    (* Hack: be more permissive toward a way that a ppx can mishandle an
       attribute, which is to duplicate the top-level Jane Syntax
       attribute.
    *)
    let rec remove_top_level_attributes expr =
      match expand_n_ary_expr expr with
      | Some (Top_level, unconsumed_attributes) ->
          remove_top_level_attributes
            { expr with pexp_attributes = unconsumed_attributes }
      | _ -> expr
    in
    fun expr ->
      let expr = remove_top_level_attributes expr in
      match expr.pexp_desc with
      | Pexp_fun _ | Pexp_newtype _ -> Some (extract_fun_params expr)
      | Pexp_function cases ->
          let n_ary =
            function_without_additional_params cases None expr.pexp_loc
          in
          Some (n_ary, expr.pexp_attributes)
      | _ -> begin
          match check_constraint expr with
          | Some (constraint_, { pexp_desc = Pexp_function cases }) ->
              let n_ary =
                function_without_additional_params cases (Some constraint_)
                  expr.pexp_loc
              in
              Some (n_ary, expr.pexp_attributes)
          | _ -> None
        end

  let n_ary_function_expr ext x =
    let suffix = Attribute_node.to_suffix ext in
    Expression.make_jane_syntax feature suffix x

  let expr_of =
    let add_param ?after_fun_attribute param body =
      let fun_ =
        match param with
        | Pparam_val (label, default, pat) ->
            (Ast_helper.Exp.fun_ label default pat body
              [@alert "-prefer_jane_syntax"])
        | Pparam_newtype (newtype, loc) ->
            let loc = Location.ghostify loc in
            Ast_helper.Exp.newtype newtype body ~loc
      in
      match after_fun_attribute with
      | None -> fun_
      | Some after_fun -> n_ary_function_expr (Fun_then after_fun) fun_
    in
    fun ~loc (params, constraint_, function_body) ->
      (* See Note [Wrapping with make_entire_jane_syntax] *)
      Expression.make_entire_jane_syntax ~loc feature (fun () ->
        let body =
          match function_body with
          | Pfunction_body body -> body
          | Pfunction_cases (cases, loc, attrs) ->
              (Ast_helper.Exp.function_ cases ~loc ~attrs
                 [@alert "-prefer_jane_syntax"])
        in
        let possibly_constrained_body =
          match constraint_ with
          | None -> body
          | Some { alloc_mode; type_constraint } ->
              let constrained_body =
                let loc = Location.ghostify body.pexp_loc in
                match type_constraint with
                | Pconstraint ty -> Ast_helper.Exp.constraint_ body ty ~loc
                | Pcoerce (ty1, ty2) -> Ast_helper.Exp.coerce body ty1 ty2 ~loc
              in
              match alloc_mode with
              | Local -> n_ary_function_expr Local_constraint constrained_body
              | Global -> constrained_body
        in
        match params with
        | [] -> possibly_constrained_body
        | params ->
            let init_params, last_param = Misc.split_last params in
            let after_fun_attribute : Attribute_node.after_fun option =
              match constraint_, function_body with
              | Some _, Pfunction_cases _ -> Some Constraint_then_cases
              | None, Pfunction_cases _ -> Some Cases
              | Some _, Pfunction_body _ -> None
              | None, Pfunction_body _ -> None
            in
            let body_with_last_param =
              add_param last_param ?after_fun_attribute
                possibly_constrained_body
            in
            List.fold_right add_param init_params body_with_last_param)
end

(** [include functor] *)
module Include_functor = struct
  type signature_item =
    | Ifsig_include_functor of include_description

  type structure_item =
    | Ifstr_include_functor of include_declaration

  let feature : Feature.t = Language_extension Include_functor

  let sig_item_of ~loc = function
    | Ifsig_include_functor incl ->
        (* See Note [Wrapping with make_entire_jane_syntax] *)
        Signature_item.make_entire_jane_syntax ~loc feature (fun () ->
          Ast_helper.Sig.include_ incl)

  let of_sig_item sigi = match sigi.psig_desc with
    | Psig_include incl -> Ifsig_include_functor incl
    | _ -> failwith "Malformed [include functor] in signature"

  let str_item_of ~loc = function
    | Ifstr_include_functor incl ->
        (* See Note [Wrapping with make_entire_jane_syntax] *)
        Structure_item.make_entire_jane_syntax ~loc feature (fun () ->
          Ast_helper.Str.include_ incl)

  let of_str_item stri = match stri.pstr_desc with
    | Pstr_include incl -> Ifstr_include_functor incl
    | _ -> failwith "Malformed [include functor] in structure"
end

(** Module strengthening *)
module Strengthen = struct
  type nonrec module_type =
    { mty : Parsetree.module_type; mod_id : Longident.t Location.loc }

  let feature : Feature.t = Language_extension Module_strengthening

  (* Encoding: [S with M] becomes [functor (_ : S) -> (module M)], where
     the [(module M)] is a [Pmty_alias].  This isn't syntax we can write, but
     [(module M)] can be the inferred type for [M], so this should be fine. *)

  let mty_of ~loc { mty; mod_id } =
    (* See Note [Wrapping with make_entire_jane_syntax] *)
    Module_type.make_entire_jane_syntax ~loc feature (fun () ->
      Ast_helper.Mty.functor_ (Named (Location.mknoloc None, mty))
        (Ast_helper.Mty.alias mod_id))

  (* Returns remaining unconsumed attributes *)
  let of_mty mty = match mty.pmty_desc with
    | Pmty_functor(Named(_, mty), {pmty_desc = Pmty_alias mod_id}) ->
       { mty; mod_id }, mty.pmty_attributes
    | _ -> failwith "Malformed strengthened module type"
end

module Unboxed_constants = struct
  type t =
    | Float of string * char option
    | Integer of string * char

  type expression = t
  type pattern = t

  let feature : Feature.t = Language_extension Layouts

  let fail_malformed ~loc =
    Location.raise_errorf ~loc "Malformed unboxed numeric literal"

  let of_constant ~loc = function
    | Pconst_float (x, suffix) -> Float (x, suffix)
    | Pconst_integer (x, Some suffix) -> Integer (x, suffix)
    | Pconst_integer (_, None) ->
        Location.raise_errorf ~loc
          "Malformed unboxed int literal: suffix required"
    | _ -> fail_malformed ~loc


  (* Returns remaining unconsumed attributes *)
  let of_expr expr =
    let loc = expr.pexp_loc in
    match expr.pexp_desc with
    | Pexp_constant const -> of_constant ~loc const, expr.pexp_attributes
    | _ -> fail_malformed ~loc

  (* Returns remaining unconsumed attributes *)
  let of_pat pat =
    let loc = pat.ppat_loc in
    match pat.ppat_desc with
    | Ppat_constant const -> of_constant ~loc const, pat.ppat_attributes
    | _ -> fail_malformed ~loc

  let constant_of = function
    | Float (x, suffix) -> Pconst_float (x, suffix)
    | Integer (x, suffix) -> Pconst_integer (x, Some suffix)

  let expr_of ~loc t =
    let constant = constant_of t in
    Expression.make_entire_jane_syntax ~loc feature (fun () ->
      Ast_helper.Exp.constant constant)

  let pat_of ~loc t =
    let constant = constant_of t in
    Pattern.make_entire_jane_syntax ~loc feature (fun () ->
      Ast_helper.Pat.constant constant)
end

(******************************************************************************)
(** The interface to our novel syntax, which we export *)

module type AST = sig
  type t
  type ast

  val of_ast : ast -> t option
end

module Core_type = struct
  type t = |

  let of_ast_internal (feat : Feature.t) _typ = match feat with
    | _ -> None

  let of_ast = Core_type.make_of_ast ~of_ast_internal
end

module Constructor_argument = struct
  type t = |

  let of_ast_internal (feat : Feature.t) _carg = match feat with
    | _ -> None

  let of_ast = Constructor_argument.make_of_ast ~of_ast_internal
end

module Expression = struct
  type t =
    | Jexp_comprehension   of Comprehensions.expression
    | Jexp_immutable_array of Immutable_arrays.expression
    | Jexp_unboxed_constant of Unboxed_constants.expression
    | Jexp_n_ary_function  of N_ary_functions.expression

  let of_ast_internal (feat : Feature.t) expr = match feat with
    | Language_extension Comprehensions ->
      let expr, attrs = Comprehensions.comprehension_expr_of_expr expr in
      Some (Jexp_comprehension expr, attrs)
    | Language_extension Immutable_arrays ->
      let expr, attrs = Immutable_arrays.of_expr expr in
      Some (Jexp_immutable_array expr, attrs)
    | Language_extension Layouts ->
        let expr, attrs = Unboxed_constants.of_expr expr in
        Some (Jexp_unboxed_constant expr, attrs)
    | Builtin -> begin
        match N_ary_functions.of_expr expr with
        | Some (expr, attrs) -> Some (Jexp_n_ary_function expr, attrs)
        | None -> None
      end
    | _ -> None

  let of_ast = Expression.make_of_ast ~of_ast_internal

  let expr_of ~loc ~attrs t =
    let expr =
      match t with
      | Jexp_comprehension x    -> Comprehensions.expr_of    ~loc x
      | Jexp_immutable_array x  -> Immutable_arrays.expr_of  ~loc x
      | Jexp_unboxed_constant x -> Unboxed_constants.expr_of ~loc x
      | Jexp_n_ary_function   x -> N_ary_functions.expr_of    ~loc x
    in
    (* Performance hack: save an allocation if [attrs] is empty. *)
    match attrs with
    | [] -> expr
    | _ :: _ as attrs ->
        (* See Note [Outer attributes at end] *)
        { expr with pexp_attributes = expr.pexp_attributes @ attrs }
end

module Pattern = struct
  type t =
    | Jpat_immutable_array of Immutable_arrays.pattern
    | Jpat_unboxed_constant of Unboxed_constants.pattern

  let of_ast_internal (feat : Feature.t) pat = match feat with
    | Language_extension Immutable_arrays ->
      let expr, attrs = Immutable_arrays.of_pat pat in
      Some (Jpat_immutable_array expr, attrs)
    | Language_extension Layouts ->
      let pat, attrs = Unboxed_constants.of_pat pat in
      Some (Jpat_unboxed_constant pat, attrs)
    | _ -> None

  let of_ast = Pattern.make_of_ast ~of_ast_internal

  let pat_of ~loc ~attrs t =
    let pat =
      match t with
      | Jpat_immutable_array x -> Immutable_arrays.pat_of ~loc x
      | Jpat_unboxed_constant x -> Unboxed_constants.pat_of ~loc x
    in
    (* Performance hack: save an allocation if [attrs] is empty. *)
    match attrs with
    | [] -> pat
    | _ :: _ as attrs ->
        (* See Note [Outer attributes at end] *)
        { pat with ppat_attributes = pat.ppat_attributes @ attrs }
end

module Module_type = struct
  type t =
    | Jmty_strengthen of Strengthen.module_type

  let of_ast_internal (feat : Feature.t) mty = match feat with
    | Language_extension Module_strengthening ->
      let mty, attrs = Strengthen.of_mty mty in
      Some (Jmty_strengthen mty, attrs)
    | _ -> None

  let of_ast = Module_type.make_of_ast ~of_ast_internal

  let mty_of ~loc ~attrs t =
    let mty =
      match t with
      | Jmty_strengthen x -> Strengthen.mty_of ~loc x
    in
    (* Performance hack: save an allocation if [attrs] is empty. *)
    match attrs with
    | [] -> mty
    | _ :: _ as attrs ->
        (* See Note [Outer attributes at end] *)
        { mty with pmty_attributes = mty.pmty_attributes @ attrs }
end

module Signature_item = struct
  type t =
    | Jsig_include_functor of Include_functor.signature_item

  let of_ast_internal (feat : Feature.t) sigi =
    match feat with
    | Language_extension Include_functor ->
      Some (Jsig_include_functor (Include_functor.of_sig_item sigi))
    | _ -> None

  let of_ast = Signature_item.make_of_ast ~of_ast_internal
end

module Structure_item = struct
  type t =
    | Jstr_include_functor of Include_functor.structure_item

  let of_ast_internal (feat : Feature.t) stri =
    match feat with
    | Language_extension Include_functor ->
      Some (Jstr_include_functor (Include_functor.of_str_item stri))
    | _ -> None

  let of_ast = Structure_item.make_of_ast ~of_ast_internal
end

module Extension_constructor = struct
  type t = |

  let of_ast_internal (feat : Feature.t) _ext = match feat with
    | _ -> None

  let of_ast = Extension_constructor.make_of_ast ~of_ast_internal
end
