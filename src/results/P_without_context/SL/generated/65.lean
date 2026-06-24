

theorem Topology.P2_implies_P1_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) :
    Topology.P1 (A := A) ∧ Topology.P3 (A := A) := by
  -- Derive P1 from P2 using `interior_subset`
  have hP1 : Topology.P1 (A := A) :=
    subset_trans h
      (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A))
  -- Use monotonicity of `closure` and `interior` to derive P3 from P2
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have hinter : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hsubset
  have hP3 : Topology.P3 (A := A) := subset_trans h hinter
  exact And.intro hP1 hP3