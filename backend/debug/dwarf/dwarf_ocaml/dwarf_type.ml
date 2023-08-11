open! Dwarf_low
open! Dwarf_high

module Uid = Shape.Uid
module DAH = Dwarf_attribute_helpers
module DS = Dwarf_state

let type_shape_to_die (type_shape : Type_shape.Type_shape.t) ~parent_proto_die =
  match type_shape with
  | Ts_other -> None
  | Ts_constr type_uid ->
    (match Uid.Tbl.find_opt Type_shape.all_type_decls type_uid with
     | None | Some { definition = Tds_other; _ } -> None
     | Some { path; definition = Tds_variant { constructors }} ->
       let type_attribute = [
         DAH.create_name (Path.name path);
         DAH.create_byte_size_exn ~byte_size:8;
       ] in
       let enumeration_type =
         Proto_die.create ~parent:(Some parent_proto_die)
           ~attribute_values:type_attribute ~tag:Dwarf_tag.Enumeration_type ()
       in
       List.iteri (fun i constructor ->
         let enumerator_attributes = [
           DAH.create_name constructor;
           DAH.create_const_value ~value:(Int64.of_int (2 * i + 1))
         ] in
         Proto_die.create_ignore ~parent:(Some enumeration_type)
           ~tag:Dwarf_tag.Enumerator ~attribute_values:enumerator_attributes ()
       ) constructors;
       Some enumeration_type)

let variant_for_var state var_uid ~parent_proto_die =
  (* CR tnowak: make this function readable *)
  let type_shape = Uid.Tbl.find_opt Type_shape.all_type_shapes var_uid in
  let die = Option.bind type_shape (type_shape_to_die ~parent_proto_die) in
  Option.value die ~default:(DS.value_type_proto_die state)
