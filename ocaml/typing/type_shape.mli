module Type_decl_shape : sig
  type tds =
    | Tds_variant of { constructors : string list }
    | Tds_other

  type t =
    { path : Path.t;
      definition : tds
    }
end


module Type_shape : sig
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

val all_type_decls : Type_decl_shape.t Shape.Uid.Tbl.t
val all_ident_types : Type_shape.t Ident.Tbl.t
val add_to_type_decls : Path.t -> Types.type_declaration -> unit
