

theorem Topology.interior_inter_closure_subset_interior_and_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ closure B) ⊆ interior A ∩ closure B := by
  intro x hx
  -- From an existing lemma we get `x ∈ interior A`.
  have hxIntA : x ∈ interior A :=
    (Topology.interior_inter_closure_subset_interior_left
        (A := A) (B := B)) hx
  -- Since `x` lies in `interior (A ∩ closure B)`, it also lies in `A ∩ closure B`.
  have hSub : (interior (A ∩ closure B) : Set X) ⊆ A ∩ closure B :=
    interior_subset
  have hxAC : x ∈ A ∩ closure B := hSub hx
  -- Extract the membership in `closure B`.
  have hxClosB : x ∈ closure B := hxAC.2
  exact And.intro hxIntA hxClosB