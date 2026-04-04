/-!
# Common interfaces for functor-model verification

This file contains only lightweight abstractions shared across modules.

- `NoDrift.lean` uses these interfaces for exact semantic preservation and
  governed no-drift.
- `KStable.lean` uses them for invariant preservation at the observable /
  K-theoretic level.

The goal is to share predicate interfaces cleanly without forcing either file to
import the other's heavier machinery.
-/

namespace EquivVerification.Common

universe u v

/--
A lightweight dependent predicate on composable updates.

`Update A B` is the type of updates from `A` to `B`; a `DependentUpdatePred`
assigns a proposition to each such update.
-/
def DependentUpdatePred {Obj : Sort u} (Update : Obj → Obj → Sort v) :=
  ∀ {A B : Obj}, Update A B → Prop

/-- Predicate marking updates that explicitly change the external contract. -/
abbrev ContractChangingPred {Obj : Sort u} (Update : Obj → Obj → Sort v) :=
  DependentUpdatePred Update

/--
Predicate expressing abstract K-stability / invariant preservation.

Intended role: this captures preservation of observable/K-theoretic invariants
without forcing concrete K-theory machinery into every module.
-/
abbrev KStablePred {Obj : Sort u} (Update : Obj → Obj → Sort v) :=
  DependentUpdatePred Update

/--
Generic governance condition:

- either an update satisfies the designated semantic/liftability condition, or it
  is explicitly contract-changing;
- if it is not contract-changing, then it is K-stable.
-/
def GovernedBy {Obj : Sort u} {Update : Obj → Obj → Sort v}
    (SemanticCondition : DependentUpdatePred Update)
    (ContractChanging : ContractChangingPred Update)
    (KStable : KStablePred Update)
    {A B : Obj} (upd : Update A B) : Prop :=
  (SemanticCondition upd ∨ ContractChanging upd) ∧
    (¬ ContractChanging upd → KStable upd)

end EquivVerification.Common
