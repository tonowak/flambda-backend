module Uid = Shape.Uid

module Type_shape : sig
  type predef =
    | String
    | Bytes
    | Float
    | Nativeint
    | Int32
    | Int64
    | Floatarray
    | Int
    | Char
    | Unboxed_float
    | Lazy_t
    | Extension_constructor

  type t =
    | Ts_constr of Shape.Uid.t * t list
    | Ts_tuple of t list
    | Ts_var of string option
    | Ts_predef of predef
    | Ts_other

  include Identifiable.S with type t := t
end

module Type_decl_shape : sig
  type tds =
    | Tds_variant of
        { simple_constructors : string list;
          complex_constructors :
            (string * (string option * Type_shape.t) list) list
        }
    | Tds_record of (string * Type_shape.t) list
    | Tds_alias of Type_shape.t
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

val type_name : Type_shape.t -> string
