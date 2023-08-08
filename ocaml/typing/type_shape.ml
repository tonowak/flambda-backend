module Type_decl_shape = struct
  type tds =
    | Tds_variant of { constructors : string list }
    | Tds_other

  type t =
    { path : Path.t;
      definition : tds
    }

  let of_type_declaration path (type_declaration : Types.type_declaration) =
    match type_declaration.type_kind with
    | Type_variant (cstr_list, _variant_repr) ->
      Format.eprintf "add_type id=%a\n%!" Path.print path;
      { path
      ; definition = Tds_variant {
          constructors = List.map
                           (fun
                             (cstr : Types.constructor_declaration)
                             -> Ident.name cstr.cd_id) cstr_list
        }
      }
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
