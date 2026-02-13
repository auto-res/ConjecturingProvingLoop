

theorem Topology.interior_closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- Inclusion related to `A`.
  have hA_sub : (A ∩ B : Set X) ⊆ A := by
    intro y hy; exact hy.1
  have hA_int : interior (A ∩ B) ⊆ interior A := interior_mono hA_sub
  have hA_cl : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono hA_int
  have hxA : x ∈ interior (closure (interior A)) :=
    (interior_mono hA_cl) hx
  -- Inclusion related to `B`.
  have hB_sub : (A ∩ B : Set X) ⊆ B := by
    intro y hy; exact hy.2
  have hB_int : interior (A ∩ B) ⊆ interior B := interior_mono hB_sub
  have hB_cl : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono hB_int
  have hxB : x ∈ interior (closure (interior B)) :=
    (interior_mono hB_cl) hx
  exact And.intro hxA hxB