import Lake
open Lake DSL

package "imp" where
  version := v!"0.1.0"

@[default_target]
lean_lib Imp where
