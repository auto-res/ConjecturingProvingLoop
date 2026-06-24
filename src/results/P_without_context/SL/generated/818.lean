

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 A) : Topology.P1 A ∧ Topology.P3 A := by
  unfold Topology.P1 Topology.P2 Topology.P3 at *
  -- Proof of P1
  have hP1 : (A : Set X) ⊆ closure (interior A) := by
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hA hx
    have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    exact hsubset hx₁
  -- Auxiliary inclusion for P3
  have hsubset' : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono hcl
  -- Proof of P3
  have hP3 : (A : Set X) ⊆ interior (closure A) :=
    Set.Subset.trans hA hsubset'
  exact And.intro hP1 hP3