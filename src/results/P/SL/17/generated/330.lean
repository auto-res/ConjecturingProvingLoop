

theorem Topology.interior_closure_interior_union_subset_interior_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Step 1: `interior A ⊆ interior (A ∪ B)`
      have hsubset_int : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
      -- Step 2: Take closures to get an inclusion on closures
      have hsubset_clos : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      -- Step 3: Apply `interior_mono` to obtain the desired inclusion
      have hsubset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_clos
      exact hsubset hxA
  | inr hxB =>
      -- The argument is symmetric for `B`
      have hsubset_int : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
      have hsubset_clos : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      have hsubset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_clos
      exact hsubset hxB