module Uid = Shape.Uid

module Type_shape = struct
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

  let predef_to_string = function
    | String -> "string"
    | Bytes -> "bytes"
    | Float -> "float"
    | Nativeint -> "nativeint"
    | Int32 -> "int32"
    | Int64 -> "int64"
    | Floatarray -> "floatarray"
    | Int -> "int"
    | Char -> "char"
    | Unboxed_float -> "float#"
    | Lazy_t -> "lazy_t"
    | Extension_constructor -> "extension_constructor"

  let predef_of_string = function
    | "string" -> Some String
    | "bytes" -> Some Bytes
    | "float" -> Some Float
    | "nativeint" -> Some Nativeint
    | "int32" -> Some Int32
    | "int64" -> Some Int64
    | "floatarray" -> Some Floatarray
    | "int" -> Some Int
    | "char" -> Some Char
    | "float#" -> Some Unboxed_float
    | "lazy_t" -> Some Lazy_t
    | "extension_constructor" -> Some Extension_constructor
    | _ -> None

  type t =
    | Ts_constr of Uid.t * t list
    | Ts_tuple of t list
    | Ts_var of string option
    | Ts_predef of predef
    | Ts_other

  let rec of_type_desc (desc : Types.type_desc) uid_of_path =
    let expr_to_t expr = of_type_desc (Types.get_desc expr) uid_of_path in
    let map_expr_list (exprs : Types.type_expr list) =
      List.map expr_to_t exprs
    in
    match desc with
    | Tconstr (path, constrs, _abbrev_memo) -> (
      match predef_of_string (Path.name path) with
      | Some predef -> Ts_predef predef
      | None -> Ts_constr (uid_of_path path, map_expr_list constrs))
    | Ttuple exprs -> Ts_tuple (map_expr_list exprs)
    | Tvar { name; layout = _ } -> Ts_var name
    | Tpoly (type_expr, []) ->
      of_type_desc (Types.get_desc type_expr) uid_of_path
    | _ -> Ts_other

  let rec print ppf = function
    | Ts_predef predef -> Format.pp_print_string ppf (predef_to_string predef)
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
      Format.fprintf ppf "Ts_var (%a)"
        (fun ppf opt -> Format.pp_print_option Format.pp_print_string ppf opt)
        name
    | Ts_other -> Format.fprintf ppf "Ts_other"

  let rec replace_tvar t ~(pairs : (t * t) list) =
    match
      List.filter_map
        (fun (from, to_) ->
          match t = from with true -> Some to_ | false -> None)
        pairs
    with
    | new_type :: _ -> new_type
    | [] -> (
      match t with
      | Ts_constr (uid, shape_list) ->
        Ts_constr (uid, List.map (replace_tvar ~pairs) shape_list)
      | Ts_tuple shape_list ->
        Ts_tuple (List.map (replace_tvar ~pairs) shape_list)
      | Ts_var name -> Ts_var name
      | Ts_predef predef -> Ts_predef predef
      | Ts_other -> Ts_other)
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
      compilation_unit : Compilation_unit.t option;
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

  let of_type_declaration compilation_unit path
      (type_declaration : Types.type_declaration) uid_of_path =
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
    { path; definition; type_params; compilation_unit }

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
    { type_params = [];
      path = t.path;
      compilation_unit = t.compilation_unit;
      definition =
        (match t.definition with
        | Tds_variant { simple_constructors; complex_constructors } ->
          Tds_variant
            { simple_constructors;
              complex_constructors =
                List.map
                  (fun (name, shape_list) ->
                    ( name,
                      List.map
                        (Type_shape.replace_tvar
                           ~pairs:(List.combine t.type_params shapes))
                        shape_list ))
                  complex_constructors
            }
        | Tds_other -> Tds_other)
    }
end

let (all_type_decls : Type_decl_shape.t Uid.Tbl.t) = Uid.Tbl.create 42

let (all_type_shapes : Type_shape.t Uid.Tbl.t) = Uid.Tbl.create 42

let add_to_type_decls path (type_decl : Types.type_declaration) uid_of_path =
  let uid = type_decl.type_uid in
  let type_decl_shape =
    Type_decl_shape.of_type_declaration
      (Compilation_unit.get_current ())
      path type_decl uid_of_path
  in
  Uid.Tbl.add all_type_decls uid type_decl_shape

let add_to_type_shapes var_uid type_desc uid_of_path =
  let type_shape = Type_shape.of_type_desc type_desc uid_of_path in
  Uid.Tbl.add all_type_shapes var_uid type_shape

let tuple_to_string (strings : string list) =
  match strings with
  | [] -> ""
  | hd :: [] -> hd
  | _ :: _ :: _ -> "(" ^ String.concat ", " strings ^ ")"

let rec type_name (type_shape : Type_shape.t) =
  match type_shape with
  | Ts_predef predef -> Type_shape.predef_to_string predef
  | Ts_other -> "unknown"
  | Ts_tuple shapes -> tuple_to_string (List.map type_name shapes)
  | Ts_var name -> "'" ^ Option.value name ~default:"?"
  | Ts_constr (type_uid, shapes) -> (
    match Uid.Tbl.find_opt all_type_decls type_uid with
    | None | Some { definition = Tds_other; _ } -> "unknown"
    | Some type_decl_shape ->
      let args = tuple_to_string (List.map type_name shapes) in
      let args = match args with "" -> args | _ -> args ^ " " in
      let compilation_unit_name =
        type_decl_shape.compilation_unit
        |> Option.map (fun x -> Compilation_unit.full_path_as_string x ^ ".")
        |> Option.value ~default:""
      in
      let name_with_compilation_unit =
        compilation_unit_name ^ Path.name type_decl_shape.path
      in
      args ^ name_with_compilation_unit)
