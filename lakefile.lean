import Lake
open Lake DSL

package arrow_poly {
  -- add configuration options here
  --moreLeancArgs := #["-UNDEBUG"]
}

lean_lib ArrowPoly {
  -- add library configuration options here
}

@[default_target]
lean_exe arrow_poly {
  root := `Main
}