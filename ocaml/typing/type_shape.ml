module Uid = Shape.Uid

module Type_decl_shape = struct
  type tds =
    | Tds_variant of { constructors : string list }
    | Tds_other

  type t =
    { path : Path.t;
      definition : tds
    }

  let is_empty_constructor_list (cstr_args : Types.constructor_declaration) =
    let length =
      match cstr_args.cd_args with
      | Cstr_tuple list -> List.length list
      | Cstr_record list -> List.length list
    in
    length == 0

  let of_type_declaration path (type_declaration : Types.type_declaration) =
    match type_declaration.type_kind with
    | Type_variant (cstr_list, _variant_repr) -> (
      let is_simple_variant =
        List.for_all is_empty_constructor_list cstr_list
      in
      match is_simple_variant with
      | false -> { path; definition = Tds_other }
      | true ->
        Format.eprintf "add_type id=%a\n%!" Path.print path;
        { path;
          definition =
            Tds_variant
              { constructors =
                  List.map
                    (fun (cstr : Types.constructor_declaration) ->
                      Ident.name cstr.cd_id)
                    cstr_list
              }
        })
    | Type_record _ | Type_abstract | Type_open ->
      { path; definition = Tds_other }

  let print_tds ppf = function
    | Tds_variant { constructors } ->
      Format.fprintf ppf "Tds_variant constructors=%a"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space
           Format.pp_print_string)
        constructors
    | Tds_other -> Format.fprintf ppf "Tds_other"

  let print ppf t =
    Format.fprintf ppf "path=%a, definition=(%a)" Path.print t.path print_tds
      t.definition
end

module Type_shape = struct
  type t =
    | Ts_constr of Uid.t
    | Ts_tuple of t list
    | Ts_other
  (* | Ttyp_var of string option * const_layout option | Ttyp_arrow of arg_label
     * core_type * core_type | Ttyp_tuple of core_type list | Ttyp_object of
     object_field list * closed_flag | Ttyp_class of Path.t * Longident.t loc *
     core_type list | Ttyp_alias of core_type * string option * const_layout
     option | Ttyp_variant of row_field list * closed_flag * label list option |
     Ttyp_poly of (string * const_layout option) list * core_type | Ttyp_package
     of package_type *)

  let rec of_type_desc (desc : Types.type_desc) uid_of_path =
    match desc with
    | Tconstr (path, constrs, _abbrev_memo) -> (
      match constrs with
      | [] -> Ts_constr (uid_of_path path)
      | _ :: _ -> Ts_other)
    | Ttuple exprs ->
      Ts_tuple
        (List.map
           (fun expr -> of_type_desc (Types.get_desc expr) uid_of_path)
           exprs)
    | _ -> Ts_other

  let rec print ppf = function
    | Ts_constr uid -> Format.fprintf ppf "Ts_constr uid=%a" Uid.print uid
    | Ts_tuple shapes ->
      Format.fprintf ppf "Ts_tuple (%a)"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
           print)
        shapes
    | Ts_other -> Format.fprintf ppf "Ts_other"
end

let all_type_decls = Uid.Tbl.create 42

let all_type_shapes = Uid.Tbl.create 42

let add_to_type_decls path (type_decl : Types.type_declaration) =
  let uid = type_decl.type_uid in
  let type_decl_shape = Type_decl_shape.of_type_declaration path type_decl in
  Uid.Tbl.add all_type_decls uid type_decl_shape

let add_to_type_shapes var_uid type_desc uid_of_path =
  let type_shape = Type_shape.of_type_desc type_desc uid_of_path in
  Uid.Tbl.add all_type_shapes var_uid type_shape
