

theorem Topology.interior_closure_interior_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- Step 1: establish monotone relationships between the pertinent sets.
  have hAB_to_A : interior (A ∩ B) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
  have hAB_to_B : interior (A ∩ B) ⊆ interior B :=
    interior_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
  have h_closure_A : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono hAB_to_A
  have h_closure_B : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono hAB_to_B
  -- Step 2: pass to interiors of the closures.
  have h_int_A : interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) :=
    interior_mono h_closure_A
  have h_int_B : interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior B)) :=
    interior_mono h_closure_B
  -- Step 3: combine the two inclusions for the desired result.
  exact And.intro (h_int_A hx) (h_int_B hx)