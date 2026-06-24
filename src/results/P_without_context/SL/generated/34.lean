

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro hP2
  -- To prove A ⊆ interior (closure A), fix an arbitrary x ∈ A.
  intro x hxA
  -- From P2, x belongs to interior (closure (interior A)).
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Since interior is monotone and closure (interior A) ⊆ closure A,
  -- we have interior (closure (interior A)) ⊆ interior (closure A).
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  -- Hence, x ∈ interior (closure A).
  exact hsubset hx₁