module Uid = Shape.Uid

module Type_shape : sig
  type t =
    | Ts_constr of Shape.Uid.t * t list
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
  val print : Format.formatter -> t -> unit
end

module Type_decl_shape : sig
  type tds =
    | Tds_variant of
        { simple_constructors : string list;
          complex_constructors : (string * Type_shape.t list) list
        }
    | Tds_other

  type t =
    { path : Path.t;
      compilation_unit : Compilation_unit.t option;
      definition : tds;
      type_params : Type_shape.t list
    }

  val print : Format.formatter -> t -> unit

  val replace_tvar : t -> Type_shape.t list -> t
end

val all_type_decls : Type_decl_shape.t Uid.Tbl.t

val all_type_shapes : Type_shape.t Uid.Tbl.t

(* Passing [Path.t -> Uid.t] instead of [Env.t] to avoid a dependency cycle. *)
val add_to_type_decls :
  Path.t -> Types.type_declaration -> (Path.t -> Uid.t) -> unit

val add_to_type_shapes : Uid.t -> Types.type_desc -> (Path.t -> Uid.t) -> unit
