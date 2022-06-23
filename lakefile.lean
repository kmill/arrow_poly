import Lake
open Lake DSL

package arrow_poly {
  -- add configuration options here
  --moreLeancArgs := #["-UNDEBUG"]
}

@[defaultTarget]
lean_exe arrow_poly {
  root := `Main
}