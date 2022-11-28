(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)


exception CFGConstructionError of string

open Tigercommon.Ll

type cfg_builder
val add_alloca:  uid * ty -> cfg_builder -> cfg_builder
val add_insn: uid option * insn -> cfg_builder ->  cfg_builder
val term_block: terminator -> cfg_builder -> cfg_builder
val start_block: lbl -> cfg_builder -> cfg_builder
val empty_cfg_builder: cfg_builder
val get_cfg: cfg_builder -> cfg

type buildlet = cfg_builder -> cfg_builder
val id_buildlet: buildlet
val seq_buildlets: buildlet list -> buildlet
