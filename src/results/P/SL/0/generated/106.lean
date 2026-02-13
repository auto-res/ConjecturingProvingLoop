

theorem P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure (A : Set X) ⊆ closure (interior A) := by
  constructor
  · intro hP1
    dsimp [Topology.P1] at hP1
    have h : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hP1
    simpa [closure_closure] using h
  · intro hSub
    dsimp [Topology.P1]
    intro x hxA
    have hxCl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    exact hSub hxCl