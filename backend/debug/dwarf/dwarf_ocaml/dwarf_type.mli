open! Dwarf_low
open! Dwarf_high
module Uid = Shape.Uid

val variant_for_var :
  Dwarf_state.t -> Uid.t -> parent_proto_die:Proto_die.t -> Proto_die.reference
