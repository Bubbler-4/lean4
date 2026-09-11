/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Producers.Range

@[expose] public section

open Std.Iterators

namespace Std.PRange

@[unbox] structure ReverseClosedIterator (α : Type u) where
  next : Option α
  lowerBound : α

@[unbox] structure ReverseOpenIterator (α : Type u) where
  next : Option α
  lowerBound : α

@[unbox] structure ReverseUnboundedIterator (α : Type u) where
  next : Option α

private def closedStep [DownwardEnumerable α] [LE α] [DecidableLE α]
    (it : Iter (α := ReverseClosedIterator α) α) :=
  match it.internalState.next with
  | some next => if it.internalState.lowerBound ≤ next then
      .yield ⟨⟨pred? next, it.internalState.lowerBound⟩⟩ next
    else .done
  | none => .done

instance [DownwardEnumerable α] [LE α] [DecidableLE α] :
    Iterator (ReverseClosedIterator α) Id α where
  IsPlausibleStep it step := step = closedStep it
  step it := pure ⟨closedStep it, rfl⟩

private def openStep [DownwardEnumerable α] [LT α] [DecidableLT α]
    (it : Iter (α := ReverseOpenIterator α) α) :=
  match it.internalState.next with
  | some next => if it.internalState.lowerBound < next then
      .yield ⟨⟨pred? next, it.internalState.lowerBound⟩⟩ next
    else .done
  | none => .done

instance [DownwardEnumerable α] [LT α] [DecidableLT α] :
    Iterator (ReverseOpenIterator α) Id α where
  IsPlausibleStep it step := step = openStep it
  step it := pure ⟨openStep it, rfl⟩

private def unboundedStep [DownwardEnumerable α]
    (it : Iter (α := ReverseUnboundedIterator α) α) :=
  match it.internalState.next with
  | some next => .yield ⟨⟨pred? next⟩⟩ next
  | none => .done

instance [DownwardEnumerable α] : Iterator (ReverseUnboundedIterator α) Id α where
  IsPlausibleStep it step := step = unboundedStep it
  step it := pure ⟨unboundedStep it, rfl⟩

end Std.PRange

open Std.PRange

/-- Iterates over the range in decreasing order. -/
def Std.Rcc.iterRev (r : Rcc α) : Iter (α := ReverseClosedIterator α) α := ⟨⟨some r.upper, r.lower⟩⟩
/-- Iterates over the range in decreasing order. -/
def Std.Rco.iterRev [DownwardEnumerable α] (r : Rco α) : Iter (α := ReverseClosedIterator α) α := ⟨⟨pred? r.upper, r.lower⟩⟩
/-- Iterates over the range in decreasing order. -/
def Std.Rci.iterRev [Greatest? α] (r : Rci α) : Iter (α := ReverseClosedIterator α) α := ⟨⟨greatest?, r.lower⟩⟩
/-- Iterates over the range in decreasing order. -/
def Std.Roc.iterRev (r : Roc α) : Iter (α := ReverseOpenIterator α) α := ⟨⟨some r.upper, r.lower⟩⟩
/-- Iterates over the range in decreasing order. -/
def Std.Roo.iterRev [DownwardEnumerable α] (r : Roo α) : Iter (α := ReverseOpenIterator α) α := ⟨⟨pred? r.upper, r.lower⟩⟩
/-- Iterates over the range in decreasing order. -/
def Std.Roi.iterRev [Greatest? α] (r : Roi α) : Iter (α := ReverseOpenIterator α) α := ⟨⟨greatest?, r.lower⟩⟩
/-- Iterates over the range in decreasing order. -/
def Std.Ric.iterRev (r : Ric α) : Iter (α := ReverseUnboundedIterator α) α := ⟨⟨some r.upper⟩⟩
/-- Iterates over the range in decreasing order. -/
def Std.Rio.iterRev [DownwardEnumerable α] (r : Rio α) : Iter (α := ReverseUnboundedIterator α) α := ⟨⟨pred? r.upper⟩⟩
/-- Iterates over the range in decreasing order. -/
def Std.Rii.iterRev [Greatest? α] (_ : Rii α) : Iter (α := ReverseUnboundedIterator α) α := ⟨⟨greatest?⟩⟩
