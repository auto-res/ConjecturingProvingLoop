

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  -- Goal: `closure A ⊆ closure (interior (closure A))`.
  -- First, rewrite `closure A` using `hP1`.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 hP1
  -- Establish the required inclusion of closures.
  have hIncl : closure (interior A) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    have : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono this
  -- Conclude the proof.
  intro x hx
  have hx' : x ∈ closure (interior A) := by
    simpa [hEq] using hx
  exact hIncl hx'