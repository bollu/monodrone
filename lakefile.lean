import Lake
open Lake DSL

package «Monodrone» where
  -- add package configuration options here

@[default_target]
lean_lib «Monodrone» where
  defaultFacets := #[LeanLib.staticFacet]
