module Uid = Shape.Uid

module Type_shape = struct
  type t =
    | Ts_constr of Uid.t * t list
    | Ts_tuple of t list
    | Ts_var of string
    | Ts_other
  (* | Ttyp_var of string option * const_layout option | Ttyp_arrow of arg_label
     * core_type * core_type | Ttyp_tuple of core_type list | Ttyp_object of
     object_field list * closed_flag | Ttyp_class of Path.t * Longident.t loc *
     core_type list | Ttyp_alias of core_type * string option * const_layout
     option | Ttyp_variant of row_field list * closed_flag * label list option |
     Ttyp_poly of (string * const_layout option) list * core_type | Ttyp_package
     of package_type *)

  let rec of_type_desc (desc : Types.type_desc) uid_of_path =
    let expr_to_t expr = of_type_desc (Types.get_desc expr) uid_of_path in
    let map_expr_list (exprs : Types.type_expr list) =
      List.map expr_to_t exprs
    in
    match desc with
    | Tconstr (path, constrs, _abbrev_memo) ->
      Ts_constr (uid_of_path path, map_expr_list constrs)
    | Ttuple exprs -> Ts_tuple (map_expr_list exprs)
    | Tvar { name; layout = _ } -> (
      match name with Some name -> Ts_var name | _ -> Ts_other)
    | _ -> Ts_other

  let rec print ppf = function
    | Ts_constr (uid, shapes) ->
      Format.fprintf ppf "Ts_constr uid=%a (%a)" Uid.print uid
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
           print)
        shapes
    | Ts_tuple shapes ->
      Format.fprintf ppf "Ts_tuple (%a)"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
           print)
        shapes
    | Ts_var name ->
      Format.fprintf ppf "Ts_var (%a)" Format.pp_print_string name
    | Ts_other -> Format.fprintf ppf "Ts_other"

  module StringMap = Map.Make (String)

  let rec replace_tvar t ~(map : t StringMap.t) =
    match t with
    | Ts_constr (uid, shape_list) ->
      Ts_constr (uid, List.map (replace_tvar ~map) shape_list)
    | Ts_tuple shape_list -> Ts_tuple (List.map (replace_tvar ~map) shape_list)
    | Ts_var name -> StringMap.find name map
    | Ts_other -> Ts_other
end

module Type_decl_shape = struct
  type tds =
    | Tds_variant of
        { simple_constructors : string list;
          complex_constructors : (string * Type_shape.t list) list
        }
    | Tds_other

  type t =
    { path : Path.t;
      definition : tds;
      type_params : Type_shape.t list
    }

  let tuple_constructors (cstr_args : Types.constructor_declaration) uid_of_path
      =
    match cstr_args.cd_args with
    | Cstr_tuple list ->
      List.map
        (fun (type_expr, _flag) ->
          Type_shape.of_type_desc (Types.get_desc type_expr) uid_of_path)
        list
    | Cstr_record _list -> []

  let is_empty_constructor_list (cstr_args : Types.constructor_declaration) =
    let length =
      match cstr_args.cd_args with
      | Cstr_tuple list -> List.length list
      | Cstr_record list -> List.length list
    in
    length == 0

  let of_type_declaration path (type_declaration : Types.type_declaration)
      uid_of_path =
    let definition =
      match type_declaration.type_kind with
      | Type_variant (cstr_list, _variant_repr) ->
        let simple_constructors, complex_constructors =
          List.partition_map
            (fun (cstr : Types.constructor_declaration) ->
              let name = Ident.name cstr.cd_id in
              match is_empty_constructor_list cstr with
              | true -> Left name
              | false -> Right (name, tuple_constructors cstr uid_of_path))
            cstr_list
        in
        Tds_variant { simple_constructors; complex_constructors }
      | Type_record _ | Type_abstract | Type_open -> Tds_other
    in
    let type_params =
      List.map
        (fun type_expr ->
          Type_shape.of_type_desc (Types.get_desc type_expr) uid_of_path)
        type_declaration.type_params
    in
    { path; definition; type_params }

  let print_complex_constructor ppf (name, constructors) =
    Format.fprintf ppf "(%a: %a)" Format.pp_print_string name
      (Format.pp_print_list ~pp_sep:Format.pp_print_space Type_shape.print)
      constructors

  let print_tds ppf = function
    | Tds_variant { simple_constructors; complex_constructors } ->
      Format.fprintf ppf
        "Tds_variant simple_constructors=%a complex_constructors=%a"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space
           Format.pp_print_string)
        simple_constructors
        (Format.pp_print_list ~pp_sep:Format.pp_print_space
           print_complex_constructor)
        complex_constructors
    | Tds_other -> Format.fprintf ppf "Tds_other"

  let print ppf t =
    Format.fprintf ppf "path=%a, definition=(%a)" Path.print t.path print_tds
      t.definition

  let replace_tvar (t : t) (shapes : Type_shape.t list) =
    Format.eprintf "replacing tvar %a; %a; %a\n%!" print t
      (Format.pp_print_list ~pp_sep:Format.pp_print_space Type_shape.print)
      shapes
      (Format.pp_print_list ~pp_sep:Format.pp_print_space Type_shape.print)
      t.type_params;
    let type_params =
      List.map
        (fun (type_shape : Type_shape.t) ->
          match type_shape with
          | Ts_constr _ | Ts_tuple _ | Ts_other -> "TODO throw"
          | Ts_var name -> name)
        t.type_params
    in
    Format.eprintf "type_params %a\n%!"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space Format.pp_print_string)
      type_params;
    let map =
      List.combine type_params shapes
      |> List.to_seq |> Type_shape.StringMap.of_seq
    in
    { type_params = [];
      path = t.path;
      definition =
        (match t.definition with
        | Tds_variant { simple_constructors; complex_constructors } ->
          Tds_variant
            { simple_constructors;
              complex_constructors =
                List.map
                  (fun (name, shape_list) ->
                    name, List.map (Type_shape.replace_tvar ~map) shape_list)
                  complex_constructors
            }
        | Tds_other -> Tds_other)
    }
end

let all_type_decls = Uid.Tbl.create 42

let all_type_shapes = Uid.Tbl.create 42

let add_to_type_decls path (type_decl : Types.type_declaration) uid_of_path =
  let uid = type_decl.type_uid in
  let type_decl_shape =
    Type_decl_shape.of_type_declaration path type_decl uid_of_path
  in
  Uid.Tbl.add all_type_decls uid type_decl_shape

let add_to_type_shapes var_uid type_desc uid_of_path =
  let type_shape = Type_shape.of_type_desc type_desc uid_of_path in
  Uid.Tbl.add all_type_shapes var_uid type_shape
