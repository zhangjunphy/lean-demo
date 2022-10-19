import Lake
open Lake DSL

package «lean-demo» {
  -- add package configuration options here
}

lean_lib Exercises {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe «lean-demo» {
  root := `Main
}
