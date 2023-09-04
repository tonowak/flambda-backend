open! Dwarf_low
open! Dwarf_high
module Uid = Shape.Uid
module DAH = Dwarf_attribute_helpers
module DS = Dwarf_state
module SLDL = Simple_location_description_lang

let need_rvalue (type_shape : Type_shape.Type_shape.t) =
  (* The location descriptions for values that are boxed need to evaluate to the
     actual pointer ("rvalue" in the sense of Dwarf_variables_and_parameters)
     instead of a location describing where the pointer lives ("lvalue"). *)
  match type_shape with
  | Ts_other | Ts_constr _ -> false
  | Ts_tuple _ -> true
  | Ts_var _ -> false
  | Ts_predef _ -> false

let rec type_shape_to_die (type_shape : Type_shape.Type_shape.t)
    ~parent_proto_die ~fallback_die =
  (* CR tnowak: wrong parent? *)
  match type_shape with
  | Ts_other | Ts_var _ -> fallback_die
  | Ts_predef predef -> (
    match predef with
    | Int ->
      (*Proto_die.create ~parent:(Some parent_proto_die)
        ~tag:Dwarf_tag.Base_type ~attribute_values:[ DAH.create_byte_size_exn
        ~byte_size:8; DAH.create_bit_size (Int64.of_int 63);
        DAH.create_data_bit_offset ~bit_offset:(Numbers.Int8.of_int_exn 1);
        DAH.create_encoding ~encoding:Encoding_attribute.signed; DAH.create_name
        "int" ] (), "int"*)
      fallback_die
    | _ -> fallback_die)
  | Ts_constr (type_uid, shapes) -> (
    match Uid.Tbl.find_opt Type_shape.all_type_decls type_uid with
    | None | Some { definition = Tds_other; _ } -> fallback_die
    | Some type_decl_shape -> (
      let type_decl_shape =
        Type_shape.Type_decl_shape.replace_tvar type_decl_shape shapes
      in
      match type_decl_shape.definition with
      | Tds_other -> fallback_die
      | Tds_variant { simple_constructors; complex_constructors } -> (
        match complex_constructors with
        | [] ->
          let simple_constructor_type =
            Proto_die.create ~parent:(Some parent_proto_die)
              ~tag:Dwarf_tag.Enumeration_type
              ~attribute_values:
                [ DAH.create_byte_size_exn ~byte_size:8;
                  DAH.create_name (Type_shape.type_name type_shape) ]
              ()
          in
          List.iteri
            (fun i constructor ->
              Proto_die.create_ignore ~parent:(Some simple_constructor_type)
                ~tag:Dwarf_tag.Enumerator
                ~attribute_values:
                  [ DAH.create_const_value ~value:(Int64.of_int ((2 * i) + 1));
                    DAH.create_name constructor ]
                ())
            simple_constructors;
          simple_constructor_type
        | _ :: _ ->
          let int_or_ptr_structure =
            Proto_die.create ~parent:(Some parent_proto_die)
              ~attribute_values:
                [ DAH.create_byte_size_exn ~byte_size:8;
                  DAH.create_name (Type_shape.type_name type_shape) ]
              ~tag:Dwarf_tag.Structure_type ()
          in
          let variant_part =
            Proto_die.create ~parent:(Some int_or_ptr_structure)
              ~attribute_values:[] ~tag:Dwarf_tag.Variant_part ()
          in
          let int_or_ptr_enum =
            Proto_die.create ~parent:(Some parent_proto_die)
              ~tag:Dwarf_tag.Enumeration_type
              ~attribute_values:
                [ DAH.create_byte_size_exn ~byte_size:8;
                  DAH.create_bit_size (Int64.of_int 1);
                  DAH.create_name ("Enum ptr/immediate case " ^ (Type_shape.type_name type_shape))
                ]
              ()
          in
          List.iteri
            (fun i name ->
              Proto_die.create_ignore ~parent:(Some int_or_ptr_enum)
                ~tag:Dwarf_tag.Enumerator
                ~attribute_values:
                  [ DAH.create_name name;
                    DAH.create_const_value ~value:(Int64.of_int i) ]
                ())
            ["Pointer"; "Immediate"];
          (* CR tnowak: add comments that tell why the code is so messed up *)
          let int_or_ptr_discr =
            Proto_die.create ~parent:(Some variant_part)
              ~attribute_values:
                [ DAH.create_type ~proto_die:int_or_ptr_enum;
                  DAH.create_bit_size (Int64.of_int 1);
                  DAH.create_data_bit_offset
                    ~bit_offset:(Numbers.Int8.of_int_exn 0);
                  DAH.create_data_member_location_offset
                    ~byte_offset:(Int64.of_int 0) ]
                (*[ DAH.create_type ~proto_die:fallback_die;
                  DAH.create_data_member_location_offset
                  ~byte_offset:(Int64.of_int 0)]*)
              ~tag:Dwarf_tag.Member ()
          in
          Proto_die.add_or_replace_attribute_value variant_part
            (DAH.create_discr
               ~proto_die_reference:(Proto_die.reference int_or_ptr_discr));
          let int_case_variant =
            Proto_die.create ~parent:(Some variant_part) ~tag:Dwarf_tag.Variant
              ~attribute_values:[DAH.create_discr_value ~value:(Int64.of_int 1)]
              ()
          in
          let simple_constructor_type =
            Proto_die.create ~parent:(Some parent_proto_die)
              ~tag:Dwarf_tag.Enumeration_type
              ~attribute_values:
                [ DAH.create_byte_size_exn ~byte_size:8;
                  DAH.create_bit_size (Int64.of_int 63);
                  DAH.create_name
                    ((Type_shape.type_name type_shape) ^ " " ^ String.concat "," simple_constructors)
                ]
              ()
          in
          List.iteri
            (fun i constructor ->
              Proto_die.create_ignore ~parent:(Some simple_constructor_type)
                ~tag:Dwarf_tag.Enumerator
                ~attribute_values:
                  [ DAH.create_const_value ~value:(Int64.of_int i);
                    DAH.create_name constructor ]
                ())
            simple_constructors;
          Proto_die.create_ignore ~parent:(Some int_case_variant)
            ~tag:Dwarf_tag.Member
            ~attribute_values:
              [ DAH.create_type ~proto_die:simple_constructor_type;
                DAH.create_bit_size (Int64.of_int 63);
                DAH.create_data_member_location_offset
                  ~byte_offset:(Int64.of_int 0);
                DAH.create_data_bit_offset
                  ~bit_offset:(Numbers.Int8.of_int_exn 1) ]
            ();
          let ptr_case_variant =
            Proto_die.create ~parent:(Some variant_part) ~tag:Dwarf_tag.Variant
              ~attribute_values:[DAH.create_discr_value ~value:(Int64.of_int 0)]
              ()
          in
          let ptr_case_structure =
            Proto_die.create ~parent:(Some parent_proto_die)
              ~tag:Dwarf_tag.Structure_type
              ~attribute_values:
                [ DAH.create_byte_size_exn ~byte_size:8;
                  DAH.create_ocaml_offset_record_from_pointer
                    ~value:(Int64.of_int (-8));
                  DAH.create_name
                    ("variant_part " ^ (Type_shape.type_name type_shape) ^ " "
                    ^ String.concat "," (List.map fst complex_constructors)) ]
              ()
          in
          let ptr_case_pointer_to_structure =
            Proto_die.create ~parent:(Some parent_proto_die)
              ~tag:Dwarf_tag.Reference_type
              ~attribute_values:
                [ DAH.create_byte_size_exn ~byte_size:8;
                  DAH.create_type ~proto_die:ptr_case_structure ]
              ()
          in
          Proto_die.create_ignore ~parent:(Some ptr_case_variant)
            ~tag:Dwarf_tag.Member
            ~attribute_values:
              [ DAH.create_type ~proto_die:ptr_case_pointer_to_structure;
                DAH.create_data_member_location_offset
                  ~byte_offset:(Int64.of_int 0) ]
            ();
          let ptr_case_variant_part =
            Proto_die.create ~parent:(Some ptr_case_structure)
              ~attribute_values:[] ~tag:Dwarf_tag.Variant_part ()
          in
          let ptr_case_enum =
            Proto_die.create ~parent:(Some parent_proto_die)
              ~tag:Dwarf_tag.Enumeration_type
              ~attribute_values:
                [ DAH.create_byte_size_exn ~byte_size:1;
                  DAH.create_name
                    ((Type_shape.type_name type_shape) ^ " "
                    ^ String.concat "," (List.map fst complex_constructors)) ]
              ()
          in
          List.iteri
            (fun i (name, constructors) ->
              Proto_die.create_ignore ~parent:(Some ptr_case_enum)
                ~tag:Dwarf_tag.Enumerator
                ~attribute_values:
                  [ DAH.create_const_value ~value:(Int64.of_int i);
                    DAH.create_name name ]
                ())
            complex_constructors;
          let ptr_case_discr =
            Proto_die.create ~parent:(Some ptr_case_variant_part)
              ~attribute_values:
                [ DAH.create_type ~proto_die:ptr_case_enum;
                  DAH.create_data_member_location_offset
                    ~byte_offset:(Int64.of_int 0) ]
              ~tag:Dwarf_tag.Member ()
          in
          Proto_die.add_or_replace_attribute_value ptr_case_variant_part
            (DAH.create_discr
               ~proto_die_reference:(Proto_die.reference ptr_case_discr));
          List.iteri
            (fun i (name, constructors) ->
              print_endline name;
              let subvariant =
                Proto_die.create ~parent:(Some ptr_case_variant_part)
                  ~tag:Dwarf_tag.Variant
                  ~attribute_values:
                    [DAH.create_discr_value ~value:(Int64.of_int i)]
                  ()
              in
              List.iteri
                (fun i shape ->
                  let field_type =
                    match need_rvalue shape with
                    | true ->
                      Proto_die.create ~parent:(Some subvariant)
                        ~tag:Dwarf_tag.Reference_type
                        ~attribute_values:
                          [ DAH.create_byte_size_exn ~byte_size:8;
                            DAH.create_type
                              ~proto_die:
                                (type_shape_to_die shape ~parent_proto_die
                                   ~fallback_die) ]
                        ()
                    | false ->
                      type_shape_to_die shape ~parent_proto_die ~fallback_die
                  in
                  Proto_die.create_ignore ~parent:(Some subvariant)
                    ~tag:Dwarf_tag.Member
                    ~attribute_values:
                      [ DAH.create_data_member_location_offset
                          ~byte_offset:(Int64.of_int (8 * (1 + i)));
                        DAH.create_byte_size_exn ~byte_size:8;
                        DAH.create_type ~proto_die:field_type ]
                    ())
                constructors)
            complex_constructors;
          int_or_ptr_structure)))
  | Ts_tuple shapes ->
    let structure_attributes =
      [DAH.create_byte_size_exn ~byte_size:(List.length shapes * 8)]
    in
    let structure_type =
      Proto_die.create ~parent:(Some parent_proto_die)
        ~tag:Dwarf_tag.Structure_type ~attribute_values:structure_attributes ()
    in
    List.iteri
      (fun i type_shape ->
        let type_die =
          type_shape_to_die type_shape ~parent_proto_die:structure_type
            ~fallback_die
        in
        let member_attributes =
          [ DAH.create_name (Format.sprintf "tuple_field%d" i);
            DAH.create_type ~proto_die:type_die;
            (match need_rvalue type_shape with
            | false ->
              DAH.create_data_member_location_offset
                ~byte_offset:(Int64.of_int (i * 8))
            | true ->
              SLDL.Rvalue.read_field_from_block_on_dwarf_stack
                ~field:(Targetint.of_int i)
              |> SLDL.of_rvalue |> SLDL.compile
              |> Single_location_description.of_simple_location_description
              |> DAH.create_data_member_location_description) ]
        in
        (* CR tnowak: remove this comment that contains code for constructing a
           Pointer_type *)
        (* let member_type = match need_rvalue type_shape with | false ->
           type_die | true -> let pointer_attributes = [
           DAH.create_byte_size_exn ~byte_size:8; DAH.create_type
           ~proto_die:type_die ] (* CR tnowak: consider making a sibling
           attribute in [structure_type] *) in let pointer_die =
           Proto_die.create ~parent:(Some parent_proto_die)
           ~tag:Dwarf_tag.Pointer_type ~attribute_values:pointer_attributes ()
           in pointer_die in let member_attributes = [ DAH.create_name
           (Format.sprintf "tuple_field%d" i);
           DAH.create_data_member_location_offset ~byte_offset:(Int64.of_int (i
           * 8)); DAH.create_type ~proto_die:member_type ] in *)
        Proto_die.create_ignore ~parent:(Some structure_type)
          ~tag:Dwarf_tag.Member ~attribute_values:member_attributes ())
      shapes;
    Proto_die.add_or_replace_attribute_value structure_type
      (DAH.create_name (Type_shape.type_name type_shape));
    structure_type

type result =
  { die : Proto_die.t;
    need_rvalue : bool
  }

let variant_for_var state var_uid ~parent_proto_die =
  let fallback_die = DS.value_type_proto_die state in
  match Uid.Tbl.find_opt Type_shape.all_type_shapes var_uid with
  | None -> { die = fallback_die; need_rvalue = false }
  | Some type_shape ->
    let die = type_shape_to_die type_shape ~parent_proto_die ~fallback_die in
    { die; need_rvalue = need_rvalue type_shape }
