/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.Classes

public section

namespace Std.PRange

/--
This typeclass provides predecessor operations for descending enumerations.
-/
@[ext]
class DownwardEnumerable (α : Type u) where
  /-- Maps an element to its predecessor, or `none` if it has none. -/
  pred? : α → Option α
  /-- Maps an element to its `n`-th predecessor, or `none` if it does not exist. -/
  predMany? (n : Nat) (a : α) : Option α := Nat.repeat (· >>= pred?) n (some a)

export DownwardEnumerable (pred? predMany?)

/-- Optionally provides the greatest element of a type. -/
class Greatest? (α : Type u) where
  /-- Returns the greatest element, or `none` when the type is empty. -/
  greatest? : Option α

export Greatest? (greatest?)

end Std.PRange
