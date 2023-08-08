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
  ;;

  let of_type_declaration path (type_declaration : Types.type_declaration) =
    match type_declaration.type_kind with
    | Type_variant (cstr_list, _variant_repr) ->
      let is_simple_variant =
        List.for_all is_empty_constructor_list cstr_list
      in
      (match is_simple_variant with
      | false -> { path; definition = Tds_other }
      | true ->
        Format.eprintf "add_type id=%a\n%!" Path.print path;
        { path
        ; definition = Tds_variant {
            constructors = List.map
              (fun (cstr : Types.constructor_declaration) -> Ident.name cstr.cd_id)
              cstr_list
          }
        })
    | Type_record _ | Type_abstract | Type_open ->
      { path; definition = Tds_other }
end

module Type_shape = struct
  type t =
    | Ts_constr of Shape.Uid.t
    | Ts_other
  (* | Ttyp_var of string option * const_layout option | Ttyp_arrow of arg_label
     * core_type * core_type | Ttyp_tuple of core_type list | Ttyp_object of
     object_field list * closed_flag | Ttyp_class of Path.t * Longident.t loc *
     core_type list | Ttyp_alias of core_type * string option * const_layout
     option | Ttyp_variant of row_field list * closed_flag * label list option |
     Ttyp_poly of (string * const_layout option) list * core_type | Ttyp_package
     of package_type *)
end

let all_type_decls = Shape.Uid.Tbl.create 42
let all_ident_types = Ident.Tbl.create 42

let add_to_type_decls path (type_decl : Types.type_declaration) =
  let uid = type_decl.type_uid in
  let type_decl_shape = Type_decl_shape.of_type_declaration path type_decl in
  Shape.Uid.Tbl.add all_type_decls uid type_decl_shape
