open! Dwarf_low
open! Dwarf_high
module Uid = Shape.Uid

val variable_to_die :
  Dwarf_state.t -> Uid.t -> parent_proto_die:Proto_die.t -> Proto_die.reference
