/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Lake
open Lake DSL

/-! # Build configuration for finite-causal-control -/

package «finite-causal-control» where
  leanOptions := #[⟨`autoImplicit, false⟩]
  weakLeanArgs := #["-j2"]
  moreGlobalServerArgs := #["-j2"]

require «finite-relative-entropy» from git
  "https://github.com/abenenson/finite-relative-entropy" @
    "3973d752cc4a2b978e2743a159a6ee1182f93c4a"

@[default_target]
lean_lib FiniteCausalControl

@[default_target]
lean_lib FiniteCausalControlExamples
