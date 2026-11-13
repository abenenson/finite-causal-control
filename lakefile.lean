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
    "ed8aadca604ae6ef79b6cf2e66dcd6157d070318"

@[default_target]
lean_lib FiniteCausalControl

@[default_target]
lean_lib FiniteCausalControlExamples
