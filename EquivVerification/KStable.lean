import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Category.Grp.Basic
import EquivVerification.Common

open CategoryTheory
open EquivVerification.Common

/-!
# K-stability for functor models

`NoDrift.lean` treats exact semantic preservation: updates preserve and reflect
semantic equivalence of parameter states.

This file is the lightweight categorical companion: it treats preservation of
observable / K-theoretic invariants. The shared interfaces in
`EquivVerification.Common` let governance statements talk abstractly about
stability conditions without forcing exact semantic arguments to depend on
categorical machinery.

In the paper’s language, K-stability means that the induced morphism in the
observable/K-theoretic image is an isomorphism. This is an invariant-preservation
condition: distinct from, but compatible with, exact no-drift.
-/

universe u v

variable {D : Type u} [Category.{v} D]

/-- A default observable functor placeholder for lightweight experimentation. -/
axiom ObservableFunctor (C : Type u) [Category C] : C ⥤ D

/-- A default K-theory functor placeholder for lightweight experimentation. -/
axiom KTheoryFunctor : D ⥤ Ab

/--
An update `f` is K-stable when its image under the observable functor followed by
the K-theory functor is an isomorphism.

In paper notation, `K(O(f))` is the induced observable / K-theoretic morphism,
and `is_K_stable` asserts that `K(O(f))` is an isomorphism.
-/
def is_K_stable {C : Type u} [Category C] {M M' : C} (f : M ⟶ M')
    (O : C ⥤ D) (K : D ⥤ Ab) : Prop :=
  IsIso (K.map (O.map f))

/--
The categorical K-stability predicate viewed through the shared abstract
interface from `EquivVerification.Common`.
-/
def categoricalKStablePred {C : Type u} [Category C] (O : C ⥤ D) (K : D ⥤ Ab) :
    KStablePred (fun A B : C => A ⟶ B) :=
  fun {_A _B} f => is_K_stable (D := D) f O K

/-- Identity morphisms are K-stable. -/
theorem id_is_K_stable {C : Type u} [Category C] (O : C ⥤ D) (K : D ⥤ Ab) (M : C) :
    is_K_stable (D := D) (𝟙 M) O K := by
  simpa [is_K_stable] using (inferInstance : IsIso (K.map (O.map (𝟙 M))))

/-- Composition of K-stable morphisms is K-stable. -/
theorem comp_is_K_stable {C : Type u} [Category C] {M N P : C}
    {f : M ⟶ N} {g : N ⟶ P} (O : C ⥤ D) (K : D ⥤ Ab)
    (hf : is_K_stable (D := D) f O K) (hg : is_K_stable (D := D) g O K) :
    is_K_stable (D := D) (f ≫ g) O K := by
  haveI : IsIso (K.map (O.map f)) := hf
  haveI : IsIso (K.map (O.map g)) := hg
  change IsIso (K.map (O.map (f ≫ g)))
  simpa [Functor.map_comp] using
    (inferInstance : IsIso (K.map (O.map f) ≫ K.map (O.map g)))

/--
Any isomorphism in the source category is K-stable, since functors preserve
isomorphisms.
-/
theorem iso_implies_K_stable {C : Type u} [Category C] {M M' : C} (f : M ⟶ M')
    (O : C ⥤ D) (K : D ⥤ Ab) [IsIso f] :
    is_K_stable (D := D) f O K := by
  simpa [is_K_stable] using (inferInstance : IsIso (K.map (O.map f)))

/--
K-stable updates preserve invariants: their observable/K-theoretic images are
isomorphic.

Paper interpretation: K-stable updates induce isomorphisms in observable
invariants.
-/
theorem k_stable_induces_iso {C : Type u} [Category C] {M M' : C} (f : M ⟶ M')
    (O : C ⥤ D) (K : D ⥤ Ab) (h : is_K_stable (D := D) f O K) :
    Nonempty (K.obj (O.obj M) ≅ K.obj (O.obj M')) := by
  haveI : IsIso (K.map (O.map f)) := h
  exact ⟨asIso (K.map (O.map f))⟩

/-- Compatibility wrapper retaining the original theorem name. -/
theorem k_stable_preserves_invariants {C : Type u} [Category C] {M M' : C} (f : M ⟶ M')
    (O : C ⥤ D) (K : D ⥤ Ab) (h : is_K_stable (D := D) f O K) :
    Nonempty (K.obj (O.obj M) ≅ K.obj (O.obj M')) :=
  k_stable_induces_iso (D := D) f O K h
