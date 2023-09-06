open! Dwarf_low
open! Dwarf_high
module Uid = Shape.Uid
module DAH = Dwarf_attribute_helpers
module DS = Dwarf_state
module SLDL = Simple_location_description_lang

let rec need_rvalue (type_shape : Type_shape.Type_shape.t) =
  (* The location descriptions for values that are boxed need to evaluate to the
     actual pointer ("rvalue" in the sense of Dwarf_variables_and_parameters)
     instead of a location describing where the pointer lives ("lvalue"). *)
  match type_shape with
  | Ts_constr (uid, _shapes) -> (
    match Uid.Tbl.find_opt Type_shape.all_type_decls uid with
    | Some { definition = Tds_record _; _ } -> true
    | Some { definition = Tds_variant _; _ } -> false
    | Some { definition = Tds_alias shape; _ } -> need_rvalue shape
    | Some { definition = Tds_other; _ } -> false
    | None -> false)
  | Ts_tuple _ -> true
  | Ts_var _ -> false
  | Ts_predef (Array, _) -> true
  | Ts_predef _ -> false
  | Ts_other -> false

let wrap_die_under_a_pointer ~proto_die ~reference ~parent_proto_die =
  Proto_die.create_ignore ~reference ~parent:(Some parent_proto_die)
    ~tag:Dwarf_tag.Reference_type
    ~attribute_values:[
      DAH.create_byte_size_exn ~byte_size:8;
      DAH.create_type ~proto_die
    ]
    ()

let array_type ~parent_proto_die ~array_type_reference ~array_type_shape
    ~element_type_reference ~cache ~fallback_die =
  let array_type_die =
    Proto_die.create ~parent:(Some parent_proto_die) ~tag:Dwarf_tag.Array_type
      ~attribute_values:
        [ DAH.create_name (Type_shape.type_name array_type_shape);
          DAH.create_type_from_reference
            ~proto_die_reference:element_type_reference;
          (* We can't use DW_AT_byte_size or DW_AT_bit_size since we don't know
             how large the array might be. *)
          (* DW_AT_byte_stride probably isn't required strictly speaking, but
             let's add it for the avoidance of doubt. *)
          DAH.create_byte_stride ~bytes:(Numbers.Int8.of_int_exn Arch.size_addr)
        ]
      ()
  in
  (* let get_num_elements = let module O = Dwarf_operator in let module Uint8 =
     Numbers.Uint8 in [ (* Load the address of the array *)
     O.DW_op_push_object_address; (* Move back to the header *) O.DW_op_const1u
     (Uint8.of_nonnegative_int_exn Arch.size_addr); O.DW_op_minus; (* Load the
     header *) O.DW_op_deref; (* Extract the size field, in words *)
     O.DW_op_const1u (Uint8.of_nonnegative_int_exn 10); O.DW_op_shr ] |>
     Single_location_description.of_simple_location_description in *)
  Proto_die.create_ignore ~parent:(Some array_type_die)
    ~tag:Dwarf_tag.Subrange_type
    ~attribute_values:
      [ (* Thankfully, all that lldb cares about is DW_AT_count. *)
        DAH.create_count_const 0L (* DAH.create_count get_num_elements *) ]
    ();
  wrap_die_under_a_pointer ~proto_die:array_type_die ~reference:array_type_reference ~parent_proto_die

let create_char_die ~reference ~parent_proto_die =
  let enum =
    Proto_die.create ~reference ~parent:(Some parent_proto_die)
      ~tag:Dwarf_tag.Enumeration_type
      ~attribute_values:
        [DAH.create_name "char"; DAH.create_byte_size_exn ~byte_size:8]
      ()
  in
  List.iter
    (fun i ->
      Proto_die.create_ignore ~parent:(Some enum) ~tag:Dwarf_tag.Enumerator
        ~attribute_values:
          [ DAH.create_const_value ~value:(Int64.of_int ((2 * i) + 1));
            DAH.create_name (Printf.sprintf "%C" (Char.chr i)) ]
        ())
    (List.init 256 (fun i -> i))

let create_unboxed_float_die ~reference ~parent_proto_die =
  Proto_die.create_ignore ~reference ~parent:(Some parent_proto_die)
    ~tag:Dwarf_tag.Base_type
    ~attribute_values:
      [ DAH.create_name "float#";
        DAH.create_byte_size_exn ~byte_size:8;
        DAH.create_encoding ~encoding:Encoding_attribute.float ]
    ()

let create_typedef_die ~reference ~parent_proto_die ~child_die ~name =
  Proto_die.create_ignore ~reference ~parent:(Some parent_proto_die)
    ~tag:Dwarf_tag.Typedef
    ~attribute_values:
      [ DAH.create_name name;
        DAH.create_type_from_reference ~proto_die_reference:child_die ]
    ()

let create_record_die ~reference ~parent_proto_die ~name ~fields =
  let structure =
    Proto_die.create ~parent:(Some parent_proto_die)
      ~tag:Dwarf_tag.Structure_type
      ~attribute_values:
        [ DAH.create_byte_size_exn ~byte_size:(8 * List.length fields);
          DAH.create_name name ]
      ()
  in
  List.iteri
    (fun i (field_name, field_die) ->
      Proto_die.create_ignore ~parent:(Some structure) ~tag:Dwarf_tag.Member
        ~attribute_values:
          [ DAH.create_name field_name;
            DAH.create_type_from_reference ~proto_die_reference:field_die;
            DAH.create_data_member_location_offset
              ~byte_offset:(Int64.of_int (8 * i)) ]
        ())
    fields;
  wrap_die_under_a_pointer ~proto_die:structure ~reference ~parent_proto_die

let create_simple_variant_die ~reference ~parent_proto_die ~name ~simple_constructors =
  let enum =
    Proto_die.create ~reference ~parent:(Some parent_proto_die)
      ~tag:Dwarf_tag.Enumeration_type
      ~attribute_values:
        [DAH.create_byte_size_exn ~byte_size:8; DAH.create_name name]
      ()
  in
  List.iteri
    (fun i constructor ->
       Proto_die.create_ignore ~parent:(Some enum)
         ~tag:Dwarf_tag.Enumerator
         ~attribute_values:
           [ DAH.create_const_value ~value:(Int64.of_int ((2 * i) + 1));
             DAH.create_name constructor ]
         ())
    simple_constructors

(*
let create_complex_variant_die ~reference ~parent_proto_die ~name ~simple_constructors ~complex_constructors =
*)

let rec type_shape_to_die (type_shape : Type_shape.Type_shape.t)
    ~parent_proto_die ~fallback_die
    ~(cache : Proto_die.reference Type_shape.Type_shape.Tbl.t) =
  (* CR tnowak: wrong parent? *)
  match Type_shape.Type_shape.Tbl.find_opt cache type_shape with
  | Some reference -> reference
  | None -> (
    let reference = Proto_die.create_reference () in
    Type_shape.Type_shape.Tbl.add cache type_shape reference;
    let name = Type_shape.type_name type_shape in
    match type_shape with
    | Ts_other | Ts_var _ -> fallback_die
    | Ts_predef (Array, [element_type_shape]) ->
      let element_type_reference =
        type_shape_to_die element_type_shape ~parent_proto_die
          ~fallback_die ~cache
      in
      array_type ~parent_proto_die ~array_type_reference:reference
        ~array_type_shape:type_shape ~element_type_reference ~cache
        ~fallback_die;
      reference
    | Ts_predef (Char, _) ->
      create_char_die ~reference ~parent_proto_die;
      reference
    | Ts_predef (Unboxed_float, _) ->
      create_unboxed_float_die ~reference ~parent_proto_die;
      reference
    | Ts_predef (_, _) ->
      create_typedef_die ~reference ~parent_proto_die ~name
        ~child_die:fallback_die;
      reference
    | Ts_constr (type_uid, shapes) -> (
      match Uid.Tbl.find_opt Type_shape.all_type_decls type_uid with
      | None | Some { definition = Tds_other; _ } -> fallback_die
      | Some type_decl_shape -> (
        let type_decl_shape =
          Type_shape.Type_decl_shape.replace_tvar type_decl_shape shapes
        in
        match type_decl_shape.definition with
        | Tds_other -> fallback_die
        | Tds_alias alias_shape ->
          let alias_die =
            type_shape_to_die alias_shape ~parent_proto_die ~fallback_die ~cache
          in
          create_typedef_die ~reference ~parent_proto_die ~child_die:alias_die
            ~name;
          reference
        | Tds_record fields ->
          let fields =
            List.map
              (fun (field_name, type_shape) ->
                ( field_name,
                  type_shape_to_die type_shape ~parent_proto_die
                    ~fallback_die ~cache ))
              fields
          in
          create_record_die ~reference ~parent_proto_die ~name ~fields;
          reference
        | Tds_variant { simple_constructors; complex_constructors } -> (
          match complex_constructors with
          | [] ->
            create_simple_variant_die ~reference ~parent_proto_die ~name ~simple_constructors;
            reference
          | _ :: _ ->
            let int_or_ptr_structure =
              Proto_die.create ~reference ~parent:(Some parent_proto_die)
                ~attribute_values:
                  [DAH.create_byte_size_exn ~byte_size:8; DAH.create_name name]
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
                    DAH.create_name ("Enum ptr/immediate case " ^ name) ]
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
                      ~byte_offset:(Int64.of_int 0);
                    (* Making a member artificial will mark the struct as
                       artificial, which will not print the enum name when the
                       struct is a variant. *)
                    DAH.create_artificial () ]
                ~tag:Dwarf_tag.Member ()
            in
            Proto_die.add_or_replace_attribute_value variant_part
              (DAH.create_discr
                 ~proto_die_reference:(Proto_die.reference int_or_ptr_discr));
            let int_case_variant =
              Proto_die.create ~parent:(Some variant_part)
                ~tag:Dwarf_tag.Variant
                ~attribute_values:
                  [DAH.create_discr_value ~value:(Int64.of_int 1)]
                ()
            in
            let simple_constructor_type =
              Proto_die.create ~parent:(Some parent_proto_die)
                ~tag:Dwarf_tag.Enumeration_type
                ~attribute_values:
                  [ DAH.create_byte_size_exn ~byte_size:8;
                    DAH.create_bit_size (Int64.of_int 63);
                    DAH.create_name
                      (name ^ " " ^ String.concat "," simple_constructors) ]
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
              Proto_die.create ~parent:(Some variant_part)
                ~tag:Dwarf_tag.Variant
                ~attribute_values:
                  [DAH.create_discr_value ~value:(Int64.of_int 0)]
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
                      ("variant_part " ^ name ^ " "
                      ^ String.concat "," (List.map fst complex_constructors))
                  ]
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
                      (name ^ " "
                      ^ String.concat "," (List.map fst complex_constructors))
                  ]
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
                  (fun i (field_name, shape) ->
                    let field_type =
                      type_shape_to_die shape
                        ~parent_proto_die:subvariant ~fallback_die ~cache
                    in
                    let proto_die =
                      Proto_die.create ~parent:(Some subvariant)
                        ~tag:Dwarf_tag.Member
                        ~attribute_values:
                          [ DAH.create_data_member_location_offset
                              ~byte_offset:(Int64.of_int (8 * (1 + i)));
                            DAH.create_byte_size_exn ~byte_size:8;
                            DAH.create_type_from_reference
                              ~proto_die_reference:field_type ]
                        ()
                    in
                    match field_name with
                    | Some name ->
                      Proto_die.add_or_replace_attribute_value proto_die
                        (DAH.create_name name)
                    | None -> ())
                  constructors)
              complex_constructors;
            reference)))
    | Ts_tuple shapes ->
      let structure_attributes =
        [DAH.create_byte_size_exn ~byte_size:(List.length shapes * 8)]
      in
      let structure_type =
        Proto_die.create ~parent:(Some parent_proto_die)
          ~tag:Dwarf_tag.Structure_type ~attribute_values:structure_attributes
          ()
      in
      List.iteri
        (fun i type_shape ->
          let member_attributes =
            [ (*DAH.create_name (Format.sprintf "tuple_field%d" i);*)
              DAH.create_type_from_reference
                ~proto_die_reference:
                  (type_shape_to_die type_shape
                     ~parent_proto_die:structure_type ~fallback_die ~cache);
              DAH.create_data_member_location_offset
                ~byte_offset:(Int64.of_int (8 * i)) ]
          in
          Proto_die.create_ignore ~parent:(Some structure_type)
            ~tag:Dwarf_tag.Member ~attribute_values:member_attributes ())
        shapes;
      Proto_die.add_or_replace_attribute_value structure_type
        (DAH.create_name name);
      wrap_die_under_a_pointer ~proto_die:structure_type ~reference ~parent_proto_die;
      reference)

let variant_for_var state var_uid ~parent_proto_die =
  let fallback_die = Proto_die.reference (DS.value_type_proto_die state) in
  match Uid.Tbl.find_opt Type_shape.all_type_shapes var_uid with
  | None -> fallback_die
  | Some type_shape ->
    let cache = Type_shape.Type_shape.Tbl.create 42 in
    let die_reference =
      type_shape_to_die type_shape ~parent_proto_die ~fallback_die ~cache
    in
    die_reference
