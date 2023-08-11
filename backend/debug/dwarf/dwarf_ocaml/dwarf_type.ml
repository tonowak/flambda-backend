open! Dwarf_low
open! Dwarf_high
module Uid = Shape.Uid
module DAH = Dwarf_attribute_helpers
module DS = Dwarf_state

let rec type_shape_to_die (type_shape : Type_shape.Type_shape.t)
    ~parent_proto_die ~fallback_die =
  match type_shape with
  | Ts_other -> fallback_die, "value"
  | Ts_constr type_uid -> (
    match Uid.Tbl.find_opt Type_shape.all_type_decls type_uid with
    | None | Some { definition = Tds_other; _ } -> fallback_die, "value"
    | Some { path; definition = Tds_variant { constructors } } ->
      let type_attribute =
        [DAH.create_name (Path.name path); DAH.create_byte_size_exn ~byte_size:8]
      in
      let enumeration_type =
        Proto_die.create ~parent:(Some parent_proto_die)
          ~attribute_values:type_attribute ~tag:Dwarf_tag.Enumeration_type ()
      in
      List.iteri
        (fun i constructor ->
          let enumerator_attributes =
            [ DAH.create_name constructor;
              DAH.create_const_value ~value:(Int64.of_int ((2 * i) + 1)) ]
          in
          Proto_die.create_ignore ~parent:(Some enumeration_type)
            ~tag:Dwarf_tag.Enumerator ~attribute_values:enumerator_attributes ())
        constructors;
      enumeration_type, Path.name path)
  | Ts_tuple shapes ->
    let structure_attributes =
      [DAH.create_byte_size_exn ~byte_size:(List.length shapes * 8)]
    in
    let structure_type =
      Proto_die.create ~parent:(Some parent_proto_die)
        ~tag:Dwarf_tag.Structure_type ~attribute_values:structure_attributes ()
    in
    let field_type_names =
      List.mapi
        (fun i type_shape ->
          let type_die, type_name =
            type_shape_to_die type_shape ~parent_proto_die:structure_type
              ~fallback_die
          in
          let member_attributes =
            [ DAH.create_name (Format.sprintf "tuple_field%d" i);
              DAH.create_type ~proto_die:type_die;
              DAH.create_data_member_location
                ~byte_offset:(Int64.of_int (i * 8)) ]
          in
          Proto_die.create_ignore ~parent:(Some structure_type)
            ~tag:Dwarf_tag.Member ~attribute_values:member_attributes ();
          type_name)
        shapes
    in
    let name = String.concat " * " field_type_names in
    Proto_die.add_or_replace_attribute_value structure_type
      (DAH.create_name name);
    structure_type, name

let need_rvalue (type_shape : Type_shape.Type_shape.t) =
  (* The location descriptions for values that are boxed need to evaluate to the
     actual pointer ("rvalue" in the sense of Dwarf_variables_and_parameters)
     instead of a location describing where the pointer lives ("lvalue"). *)
  match type_shape with Ts_other | Ts_constr _ -> false | Ts_tuple _ -> true

type result =
  { die : Proto_die.t;
    need_rvalue : bool
  }

let variant_for_var state var_uid ~parent_proto_die =
  let fallback_die = DS.value_type_proto_die state in
  match Uid.Tbl.find_opt Type_shape.all_type_shapes var_uid with
  | None -> { die = fallback_die; need_rvalue = false }
  | Some type_shape ->
    let die, _name =
      type_shape_to_die type_shape ~parent_proto_die ~fallback_die
    in
    { die; need_rvalue = need_rvalue type_shape }
