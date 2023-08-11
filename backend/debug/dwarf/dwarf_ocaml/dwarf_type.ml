open! Dwarf_low
open! Dwarf_high

module Uid = Shape.Uid
module DAH = Dwarf_attribute_helpers
module DS = Dwarf_state

let rec type_shape_to_die (type_shape : Type_shape.Type_shape.t)
  ~parent_proto_die ~fallback_die =
  match type_shape with
  | Ts_other -> fallback_die
  | Ts_constr type_uid ->
    (match Uid.Tbl.find_opt Type_shape.all_type_decls type_uid with
     | None | Some { definition = Tds_other; _ } -> fallback_die
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
       enumeration_type)
  | Ts_tuple shapes ->
    let structure_attributes = [
      DAH.create_name "Tuple";
      DAH.create_byte_size_exn ~byte_size:(List.length shapes * 8)
    ] in
    let structure_type =
      Proto_die.create ~parent:(Some parent_proto_die)
        ~tag:Dwarf_tag.Structure_type ~attribute_values:structure_attributes ()
    in
    List.iteri (fun i type_shape ->
      let member_attributes = [
        DAH.create_name (Int.to_string i);
        DAH.create_type ~proto_die:(type_shape_to_die type_shape
          ~parent_proto_die:structure_type ~fallback_die);
        DAH.create_data_member_location ~byte_offset:(Int64.of_int 0)
      ] in
      Proto_die.create_ignore ~parent:(Some structure_type) ~tag:Dwarf_tag.Member
        ~attribute_values:member_attributes ()
    ) shapes;
    structure_type

let variant_for_var state var_uid ~parent_proto_die =
  let fallback_die = DS.value_type_proto_die state in
  match Uid.Tbl.find_opt Type_shape.all_type_shapes var_uid with
  | None -> fallback_die
  | Some type_shape -> type_shape_to_die type_shape ~parent_proto_die ~fallback_die
