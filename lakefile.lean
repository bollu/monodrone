import Lake
import Lake.Build.Library
open Lake DSL


partial def Lake.LeanLib.collectAllModulesForFatlib (self : LeanLib) : FetchM (Array Module) := do
  let mut mods := #[]
  let mut modSet := ModuleSet.empty
  for mod in (← self.getModuleArray) do
    (mods, modSet) ← go mod mods modSet
  return mods
where
  go root mods modSet := do
    let mut mods := mods
    let mut modSet := modSet
    unless modSet.contains root do
      modSet := modSet.insert root
      let imps ← root.imports.fetch
      for mod in imps do
          (mods, modSet) ← go mod mods modSet
      mods := mods.push root
    return (mods, modSet)


/-- The path to the static fat library in the package's `libDir`. -/
@[inline] def fatStaticFile (self : LeanLib) : FilePath :=
  self.pkg.nativeLibDir / nameToStaticLib s!"{self.config.libName}Fat"

@[specialize] protected def LeanLib.buildFatStatic
(self : LeanLib) : FetchM (BuildJob FilePath) := do
  withRegisterJob s!"{self.name}:fatStatic" do
  let mods := (← self.collectAllModulesForFatlib) ++ (← self.modules.fetch)
  -- trace s!"{self.name}:static{suffix} modules: {mods.map (·.name)}"
  let oJobs ← mods.concatMapM fun mod =>
    mod.nativeFacets (shouldExport := true) |>.mapM fun facet => fetch <| mod.facet facet.name
  let libFile := fatStaticFile self
  IO.println s!"successfully built: {libFile}"
  buildStaticLib libFile oJobs


library_facet fatStatic (lib : LeanLib) : FilePath :=
  LeanLib.buildFatStatic lib


package «Monodrone» where
  -- add package configuration options here

@[default_target]
lean_lib «Monodrone» where
  defaultFacets := #[`fatStatic]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "86653eb"
