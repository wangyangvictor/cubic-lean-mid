import Lake
open Lake DSL

package «TranslatedDepthSeven» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

/- The ordinary prime number theorem is used only through the individually
audited declarations `pi_alt'` and its consequences.  At this revision their
kernel axiom footprints contain no project-specific axiom or `sorryAx`. -/
require «PrimeNumberTheoremAnd» from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @
    "db0b69d008f3991b6f03bc5f59504f02eb6c724b"

@[default_target]
lean_lib «TranslatedDepthSeven» where
  -- Build exactly the strict public root and its transitive imports.
  globs := #[.one `TranslatedDepthSeven]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]
