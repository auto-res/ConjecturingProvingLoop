

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) :
    Topology.P1 (A := A) ∧ Topology.P3 (A := A) := by
  have hP1 : (A : Set X) ⊆ closure (interior A) := by
    intro x hx
    have : x ∈ interior (closure (interior A)) := h hx
    exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) this
  have h_closure_mono : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have h_interior_mono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_mono
  have hP3 : (A : Set X) ⊆ interior (closure A) := by
    intro x hx
    have : x ∈ interior (closure (interior A)) := h hx
    exact h_interior_mono this
  exact And.intro hP1 hP3