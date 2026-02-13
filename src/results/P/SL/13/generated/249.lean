

theorem Topology.closure_inter_closure_subset_inter_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ closure (B : Set X)) : Set X) ⊆
      closure A ∩ closure B := by
  intro x hx
  -- Membership in `closure A` follows from monotonicity of `closure`.
  have hxA : (x : X) ∈ closure A :=
    (closure_mono
        (Set.inter_subset_left :
          (A ∩ closure (B : Set X) : Set X) ⊆ A)) hx
  -- Membership in `closure B` is obtained similarly.
  have hxB : (x : X) ∈ closure B := by
    -- First, view `closure B` as a superset of the intersection.
    have h₁ :
        (A ∩ closure (B : Set X) : Set X) ⊆ closure B :=
      Set.inter_subset_right
    have hxB' : (x : X) ∈ closure (closure (B : Set X)) :=
      (closure_mono h₁) hx
    simpa [closure_closure] using hxB'
  exact And.intro hxA hxB