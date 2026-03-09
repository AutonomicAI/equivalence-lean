import EquivVerification.Equiv

/-!
# Stateful Functor Model Equivalence

A deterministic stateful counterpart to stateless observational equivalence,
based on finite input traces.
-/

variable {Theta : Type*}
variable {S : Type*}
variable {X : Type*}
variable {Y : Type*}

namespace Stateful

/--
Run the deterministic stateful system on a finite input list.
Returns the full output trace and the final state.
-/
def run (m_state : Theta -> S -> X -> (Y × S)) (theta : Theta) (s0 : S) : List X -> (List Y × S)
  | [] => ([], s0)
  | x :: xs =>
      let (y, s1) := m_state theta s0 x
      let (ys, sFinal) := run m_state theta s1 xs
      (y :: ys, sFinal)

/--
Running the system on a concatenated input list is equivalent to
running the first segment, then continuing from the resulting state
on the second segment.
-/
theorem run_append
    (m_state : Theta -> S -> X -> (Y × S))
    (theta : Theta) (s0 : S)
    (xs ys : List X) :
    run m_state theta s0 (xs ++ ys) =
      let (out1, s1) := run m_state theta s0 xs
      let (out2, s2) := run m_state theta s1 ys
      (out1 ++ out2, s2) := by
  induction xs generalizing s0 with
  | nil =>
      simp [run]
  | cons x xs ih =>
      simp [run, ih]

/--
Stateful semantic equivalence from a fixed initial state:
for every finite input list, output trace and final state coincide.
-/
def StatefulEquivalence (m_state : Theta -> S -> X -> (Y × S))
    (theta1 theta2 : Theta) (s0 : S) : Prop :=
  ∀ inputs : List X, run m_state theta1 s0 inputs = run m_state theta2 s0 inputs

/--
If two parameter states are statefully equivalent from an initial state `s0`,
then extending any input trace with an additional suffix preserves equality
of executions. This follows from `run_append` and expresses that equivalence
is stable under input extension.
-/
theorem stateful_equiv_extension
    (m_state : Theta -> S -> X -> (Y × S))
    {theta1 theta2 : Theta} {s0 : S}
    (h : StatefulEquivalence m_state theta1 theta2 s0)
    (xs ys : List X) :
    run m_state theta1 s0 (xs ++ ys) =
    run m_state theta2 s0 (xs ++ ys) := by
  exact h (xs ++ ys)

theorem stateful_equiv_refl (m_state : Theta -> S -> X -> (Y × S)) (theta : Theta) (s0 : S) :
    StatefulEquivalence m_state theta theta s0 := by
  intro inputs
  rfl

theorem stateful_equiv_symm (m_state : Theta -> S -> X -> (Y × S))
    (theta1 theta2 : Theta) (s0 : S) :
    StatefulEquivalence m_state theta1 theta2 s0 ->
    StatefulEquivalence m_state theta2 theta1 s0 := by
  intro h inputs
  exact (h inputs).symm

theorem stateful_equiv_trans (m_state : Theta -> S -> X -> (Y × S))
    (theta1 theta2 theta3 : Theta) (s0 : S) :
    StatefulEquivalence m_state theta1 theta2 s0 ->
    StatefulEquivalence m_state theta2 theta3 s0 ->
    StatefulEquivalence m_state theta1 theta3 s0 := by
  intro h12 h23 inputs
  exact (h12 inputs).trans (h23 inputs)

/--
For each fixed initial state, `StatefulEquivalence` is an equivalence relation on `Theta`.
-/
theorem stateful_equivalence_is_equivalence
    (m_state : Theta -> S -> X -> (Y × S)) (s0 : S) :
    Equivalence (fun t1 t2 => StatefulEquivalence m_state t1 t2 s0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact stateful_equiv_refl m_state t s0
  · intro t1 t2 h
    exact stateful_equiv_symm m_state t1 t2 s0 h
  · intro t1 t2 t3 h12 h23
    exact stateful_equiv_trans m_state t1 t2 t3 s0 h12 h23

/--
Stateful equivalence implies equality of output traces for every finite input list.
-/
theorem stateful_equiv_outputs_eq
    (m_state : Theta -> S -> X -> (Y × S))
    {theta1 theta2 : Theta} {s0 : S}
    (h : StatefulEquivalence m_state theta1 theta2 s0) :
    ∀ inputs : List X,
      (run m_state theta1 s0 inputs).fst = (run m_state theta2 s0 inputs).fst := by
  intro inputs
  exact congrArg Prod.fst (h inputs)

/--
Stateful equivalence implies equality of final states for every finite input list.
-/
theorem stateful_equiv_final_state_eq
    (m_state : Theta -> S -> X -> (Y × S))
    {theta1 theta2 : Theta} {s0 : S}
    (h : StatefulEquivalence m_state theta1 theta2 s0) :
    ∀ inputs : List X,
      (run m_state theta1 s0 inputs).snd = (run m_state theta2 s0 inputs).snd := by
  intro inputs
  exact congrArg Prod.snd (h inputs)

/--
Orbit of a parameter state under one-step governed transforms.
-/
def Orbit (theta : Theta) : Set Theta :=
  { theta' | ∃ tau : GovernedTransform Theta, tau.toFun theta = theta' }

/--
If a governed transform preserves deterministic stateful runs for all parameters,
initial states, and finite input lists, then it preserves `StatefulEquivalence`.
-/
theorem stateful_orbit_invariance
    (m_state : Theta -> S -> X -> (Y × S))
    (tau : GovernedTransform Theta)
    (hTau : ∀ theta s0 inputs,
      run m_state (tau.toFun theta) s0 inputs = run m_state theta s0 inputs)
    {theta1 theta2 : Theta} {s0 : S} :
    StatefulEquivalence m_state theta1 theta2 s0 ->
    StatefulEquivalence m_state (tau.toFun theta1) (tau.toFun theta2) s0 := by
  intro hEq inputs
  calc
    run m_state (tau.toFun theta1) s0 inputs = run m_state theta1 s0 inputs :=
      hTau theta1 s0 inputs
    _ = run m_state theta2 s0 inputs :=
      hEq inputs
    _ = run m_state (tau.toFun theta2) s0 inputs :=
      (hTau theta2 s0 inputs).symm

end Stateful
