module

@[expose] public section
set_option backward.privateInPublic true

/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

/-!
# Universe boundary for integral representations

Mathlib's `Rep ℤ G` currently requires the coefficient ring and acting group
to inhabit the same universe.  Since `ℤ : Type 0`, every representation-bearing
part of local class field theory uses this single named boundary.  Keeping the
restriction here makes a future universe-polymorphic migration searchable and
prevents individual subtrees from inventing private aliases.
-/

set_option autoImplicit false

/-- The universe-zero group boundary imposed by integral representations. -/
abbrev IntegralRepGroupType := Type 0
